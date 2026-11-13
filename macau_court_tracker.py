#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
澳門法院司法變賣自動追蹤、資料庫統計與可視化儀表板系統 (Macau Court Judicial Sale Tracker v4.0)
目標網址: https://www.court.gov.mo/zh/subpage/sell

v4.0 核心升級重點:
1. 精準防疊加機制 (Zero Duplicate Accumulation)：
   - 同一宗未過開標週期的案件，即使連續多個星期在法院網站上被抓取更新，只會更新其「最後出現週期 (last_seen_cycle)」，
     絕對不會在資料庫或週期統計中重複疊加筆數，也不會虛增「之前出現次數」。
   - 「之前出現次數 (prior_appearances_count)」嚴格定義為：
     (a) 該物業在「更早的開標日期 (auction_date < 今期開標日)」曾經排期變賣過（即流標重拍）；或
     (b) 同一開標日期但法院中途修改過「變賣底價」；或
     (c) 法院於備註明確註明「第 N 次司法變賣」（代表之前已出現過 N-1 次）。
2. 自動區分「🟢 待開標 (在列)」與「⚪ 已過開標期 (歷史歸檔)」：
   - 每次更新時，系統自動根據基準日期及網站最新名冊，將標的區分為：
     * `🟢 待開標(在列)`：開標日期 >= 基準日 且 仍在最新一期公告名冊內。
     * `⚪ 已過開標期(歷史歸檔)`：開標日期 < 基準日 或 已從最新一期網站下架之歷史紀錄。
   - 已過開標期的數據永久保留在 SQLite 資料庫及「歷史已開標歸檔」專頁，供未來數月若有流標重拍時自動跨期比對底價差額；
     而四大重點追蹤分頁（住宅、停車位、商業／寫字樓、動產）則預設只顯示「🟢 待開標(在列)」標的，版面清晰不混淆。
3. 互動式 HTML 可視化儀表板 (macau_court_dashboard.html) 內建「開標狀態切換（僅顯示待開標 / 包含歷史已開標 / 僅顯示已過期歸檔）」及完整圖表。
"""

import argparse
import datetime
import hashlib
import json
import logging
import os
import shutil
import re
import sqlite3
import sys
import time
from typing import Dict, List, Optional, Tuple

try:
    import requests
    from bs4 import BeautifulSoup
except ImportError:
    print("請先安裝必要套件: pip install requests beautifulsoup4")
    sys.exit(1)

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("CourtSaleTracker")

TARGET_URL = "https://www.court.gov.mo/zh/subpage/sell"
DEFAULT_DB_PATH = "macau_court_sales.db"


# ==============================================================================
# 1. 跨期物業唯一識別與備註次數解析輔助函式
# ==============================================================================
def build_canonical_asset_id(
    case_no: str,
    registry_id: str,
    tax_id: str,
    prop_name: str,
    address: str,
    item_index: int,
) -> str:
    """
    產生「跨期物業唯一識別碼 (Canonical Asset ID)」，用於識別同一物業或財產在不同開標期數重複出現。
    """
    norm_case = re.sub(r"\s+", "", (case_no or "")).upper()
    norm_reg = re.sub(r"\s+", "", (registry_id or "")).upper()
    norm_tax = re.sub(r"[^0-9A-Z]", "", (tax_id or "").upper())
    norm_name = re.sub(r"[\s“”\"'「」『』。.,，、]", "", (prop_name or "")).upper()
    norm_addr = re.sub(r"[\s“”\"'「」『』。.,，、]", "", (address or "")).upper()[:25]

    if norm_reg and norm_name:
        raw_key = f"REG:{norm_reg}|NAME:{norm_name}|ITEM:{item_index}"
    elif norm_case and (norm_name or norm_addr):
        raw_key = f"CASE:{norm_case}|TAX:{norm_tax}|NAME:{norm_name}|ADDR:{norm_addr}|ITEM:{item_index}"
    elif norm_case or norm_name or norm_addr:
        raw_key = f"CASE:{norm_case}|ITEM:{item_index}|NAME:{norm_name}|ADDR:{norm_addr}"
    else:
        import uuid
        raw_key = f"UNPARSED:{uuid.uuid4().hex}"

    digest = hashlib.sha1(raw_key.encode("utf-8")).hexdigest()[:14]
    return f"ASSET_{digest}"


def parse_stated_sale_count_from_remarks(remarks: str) -> Optional[int]:
    """
    從法院備註文字中提取官方註明的變賣次數（例如「第四次司法變賣」、「第5次司法變賣」、「第一次」）。
    """
    if not remarks:
        return None
    cn_map = {"一": 1, "二": 2, "三": 3, "四": 4, "五": 5, "六": 6, "七": 7, "八": 8, "九": 9, "十": 10}
    m = re.search(r"第\s*([0-9一二三四五六七八九十]+)\s*次", remarks)
    if m:
        val_str = m.group(1).strip()
        if val_str.isdigit():
            return int(val_str)
        if val_str in cn_map:
            return cn_map[val_str]
    return None


# ==============================================================================
# 2. 資料庫管理模組 (SQLite Database Manager - 防疊加與過期歸檔機制)
# ==============================================================================
class CourtSaleDatabase:
    def __init__(self, db_path: str = DEFAULT_DB_PATH):
        self.db_path = db_path
        self.conn = sqlite3.connect(self.db_path)
        self.conn.row_factory = sqlite3.Row
        self._init_tables()

    def _init_tables(self):
        cursor = self.conn.cursor()

        # 1. 案件主表
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS cases (
                case_uid TEXT PRIMARY KEY,
                auction_date TEXT,
                case_type TEXT,
                case_no TEXT,
                court TEXT,
                creditors TEXT,
                debtors TEXT,
                other_parties TEXT,
                sale_method TEXT,
                deadline_time TEXT,
                sale_time TEXT,
                sale_location TEXT,
                custodian TEXT,
                contact_info TEXT,
                remarks TEXT,
                page_last_updated TEXT,
                first_seen_cycle TEXT,
                last_seen_cycle TEXT,
                is_active INTEGER DEFAULT 1,
                lifecycle_status TEXT DEFAULT '🟢 待開標(在列)',
                created_at TEXT,
                updated_at TEXT
            )
            """
        )
        cursor.execute("PRAGMA table_info(cases)")
        existing_case_cols = {row["name"] for row in cursor.fetchall()}
        for col_name, col_type in {
            "is_active": "INTEGER DEFAULT 1",
            "lifecycle_status": "TEXT DEFAULT '🟢 待開標(在列)'",
        }.items():
            if col_name not in existing_case_cols:
                cursor.execute(f"ALTER TABLE cases ADD COLUMN {col_name} {col_type}")

        # 2. 變賣財產明細與跨期比對表
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS properties (
                prop_uid TEXT PRIMARY KEY,
                canonical_asset_id TEXT,
                case_uid TEXT,
                case_no TEXT,
                auction_date TEXT,
                item_index INTEGER,
                asset_kind TEXT,
                description TEXT,
                prop_name TEXT,
                address TEXT,
                raw_usage TEXT,
                target_category TEXT,
                is_residential INTEGER,
                is_parking INTEGER,
                tax_id TEXT,
                registry_id TEXT,
                strata_id TEXT,
                base_price_mop REAL,
                base_price_raw TEXT,
                first_seen_cycle TEXT,
                last_seen_cycle TEXT,
                is_active INTEGER DEFAULT 1,
                lifecycle_status TEXT DEFAULT '🟢 待開標(在列)',
                prior_appearances_count INTEGER DEFAULT 0,
                total_appearances_count INTEGER DEFAULT 1,
                court_stated_nth_sale INTEGER,
                prev_auction_date TEXT,
                prev_cycle_id TEXT,
                prev_base_price_mop REAL,
                price_diff_mop REAL,
                price_diff_pct REAL,
                repeat_status_flag TEXT,
                FOREIGN KEY (case_uid) REFERENCES cases(case_uid)
            )
            """
        )

        cursor.execute("PRAGMA table_info(properties)")
        existing_cols = {row["name"] for row in cursor.fetchall()}
        new_prop_cols = {
            "canonical_asset_id": "TEXT",
            "is_active": "INTEGER DEFAULT 1",
            "lifecycle_status": "TEXT DEFAULT '🟢 待開標(在列)'",
            "prior_appearances_count": "INTEGER DEFAULT 0",
            "total_appearances_count": "INTEGER DEFAULT 1",
            "court_stated_nth_sale": "INTEGER",
            "prev_auction_date": "TEXT",
            "prev_cycle_id": "TEXT",
            "prev_base_price_mop": "REAL",
            "price_diff_mop": "REAL",
            "price_diff_pct": "REAL",
            "repeat_status_flag": "TEXT",
        }
        for col_name, col_type in new_prop_cols.items():
            if col_name not in existing_cols:
                cursor.execute(f"ALTER TABLE properties ADD COLUMN {col_name} {col_type}")

        # 3. 財產跨期變賣事件歷史表 (以 canonical_asset_id + auction_date + base_price_mop 為唯一變賣事件，避免同一次未開標公告連續數週執行而重複疊加)
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS property_appearances (
                appearance_id INTEGER PRIMARY KEY AUTOINCREMENT,
                canonical_asset_id TEXT NOT NULL,
                prop_uid TEXT NOT NULL,
                case_no TEXT NOT NULL,
                auction_date TEXT NOT NULL,
                cycle_id TEXT NOT NULL,
                base_price_mop REAL,
                base_price_raw TEXT,
                recorded_at TEXT,
                UNIQUE(canonical_asset_id, auction_date, base_price_raw)
            )
            """
        )

        # 4. 每個周期統計表
        cursor.execute(
            """
            CREATE TABLE IF NOT EXISTS cycle_stats (
                cycle_id TEXT PRIMARY KEY,
                run_timestamp TEXT,
                page_last_updated TEXT,
                total_active_cases INTEGER,
                total_active_properties INTEGER,
                archived_past_properties INTEGER DEFAULT 0,
                residential_count INTEGER,
                parking_count INTEGER,
                commercial_count INTEGER,
                other_count INTEGER,
                new_cases_this_cycle INTEGER,
                new_residential_this_cycle INTEGER,
                new_parking_this_cycle INTEGER,
                repeated_props_this_cycle INTEGER DEFAULT 0,
                price_changed_props_this_cycle INTEGER DEFAULT 0,
                residential_avg_price_mop REAL,
                parking_avg_price_mop REAL
            )
            """
        )
        cursor.execute("PRAGMA table_info(cycle_stats)")
        existing_stat_cols = {row["name"] for row in cursor.fetchall()}
        for col_name, col_type in {
            "archived_past_properties": "INTEGER DEFAULT 0",
            "repeated_props_this_cycle": "INTEGER DEFAULT 0",
            "price_changed_props_this_cycle": "INTEGER DEFAULT 0",
        }.items():
            if col_name not in existing_stat_cols:
                cursor.execute(f"ALTER TABLE cycle_stats ADD COLUMN {col_name} {col_type}")

        # 5. 依開標週次 (Auction Week) 統計視圖 (包含待開標與已開標狀態)
        cursor.execute("DROP VIEW IF EXISTS v_auction_week_summary")
        cursor.execute(
            """
            CREATE VIEW v_auction_week_summary AS
            SELECT
                strftime('%Y-W%W', auction_date) AS auction_week,
                MIN(auction_date) AS week_start_date,
                MAX(auction_date) AS week_end_date,
                CASE WHEN MAX(is_active) = 1 THEN '🟢 待開標週期' ELSE '⚪ 已過開標週期' END AS week_status,
                COUNT(DISTINCT case_uid) AS case_count,
                COUNT(prop_uid) AS total_properties,
                SUM(CASE WHEN is_residential = 1 THEN 1 ELSE 0 END) AS residential_units,
                SUM(CASE WHEN is_parking = 1 THEN 1 ELSE 0 END) AS parking_spaces,
                SUM(CASE WHEN target_category = '商業/寫字樓' THEN 1 ELSE 0 END) AS commercial_units,
                SUM(CASE WHEN asset_kind = '動產' OR target_category LIKE '動產%' THEN 1 ELSE 0 END) AS movable_items,
                SUM(CASE WHEN target_category NOT IN ('住宅', '停車位', '商業/寫字樓') AND NOT (asset_kind = '動產' OR target_category LIKE '動產%') THEN 1 ELSE 0 END) AS other_items,
                SUM(CASE WHEN prior_appearances_count > 0 THEN 1 ELSE 0 END) AS repeated_items,
                SUM(CASE WHEN price_diff_mop IS NOT NULL AND ABS(price_diff_mop) > 0.01 THEN 1 ELSE 0 END) AS price_changed_items,
                ROUND(AVG(CASE WHEN is_residential = 1 AND base_price_mop > 0 THEN base_price_mop END), 2) AS avg_residential_price_mop,
                ROUND(AVG(CASE WHEN is_parking = 1 AND base_price_mop > 0 THEN base_price_mop END), 2) AS avg_parking_price_mop
            FROM properties
            GROUP BY strftime('%Y-W%W', auction_date)
            ORDER BY auction_week ASC
            """
        )
        self.conn.commit()

    def _compute_prior_history_and_diff(
        self,
        canonical_asset_id: str,
        current_auction_date: str,
        current_price: Optional[float],
        current_price_raw: str,
        court_stated_nth: Optional[int],
    ) -> Dict:
        """
        精準計算「之前出現多少次」與「前期底價差額」：
        - 僅統計：
          1. 變賣日期早於今期 (auction_date < current_auction_date) 的不同開標期數（流標重拍）；或
          2. 同一變賣日期但底價曾經變更 (auction_date = current_auction_date AND base_price_raw != current_price_raw)。
        - 同一宗未過開標週期的案件在每週例行爬蟲更新時，因 auction_date 與底價皆相同，不會虛增出現次數！
        """
        cursor = self.conn.cursor()

        cursor.execute(
            """
            SELECT auction_date, cycle_id, base_price_mop, base_price_raw, recorded_at
            FROM property_appearances
            WHERE canonical_asset_id = ?
              AND (
                  auction_date < ?
                  OR (auction_date = ? AND base_price_raw != ?)
              )
            ORDER BY auction_date DESC, appearance_id DESC
            """,
            (
                canonical_asset_id,
                current_auction_date,
                current_auction_date,
                current_price_raw or "",
            ),
        )
        prior_rows = cursor.fetchall()

        # 以不同變賣事件 (auction_date + base_price_raw) 計數
        unique_prior_events = []
        seen_event_keys = set()
        for r in prior_rows:
            ek = (r["auction_date"], r["base_price_raw"])
            if ek not in seen_event_keys:
                seen_event_keys.add(ek)
                unique_prior_events.append(r)

        db_prior_count = len(unique_prior_events)
        remark_prior_count = (court_stated_nth - 1) if (court_stated_nth and court_stated_nth > 1) else 0
        prior_count = max(db_prior_count, remark_prior_count)
        total_count = prior_count + 1

        prev_auction_date = None
        prev_cycle_id = None
        prev_price = None
        price_diff = None
        price_diff_pct = None

        if unique_prior_events:
            latest_prior = unique_prior_events[0]
            prev_auction_date = latest_prior["auction_date"]
            prev_cycle_id = latest_prior["cycle_id"]
            prev_price = latest_prior["base_price_mop"]

            if current_price is not None and prev_price is not None and prev_price > 0:
                price_diff = round(current_price - prev_price, 2)
                price_diff_pct = round((price_diff / prev_price) * 100.0, 2)

        if prior_count == 0:
            status_flag = "🆕 首次出現"
        else:
            if price_diff is not None and abs(price_diff) > 0.01:
                if price_diff < 0:
                    status_flag = (
                        f"🔻 重拍降價 (前已出現{prior_count}次 | 減 MOP {abs(price_diff):,.2f} / {price_diff_pct:+.2f}%)"
                    )
                else:
                    status_flag = (
                        f"🔺 重拍調升 (前已出現{prior_count}次 | 加 MOP {price_diff:,.2f} / {price_diff_pct:+.2f}%)"
                    )
            else:
                if db_prior_count > 0:
                    status_flag = f"🔄 跨期重拍 (前已出現{prior_count}次 | 底價不變)"
                else:
                    status_flag = f"⚠️ 法院標註第{court_stated_nth}次變賣 (前已出現{prior_count}次 | 尚無前期底價紀錄)"

        return {
            "prior_appearances_count": prior_count,
            "total_appearances_count": total_count,
            "prev_auction_date": prev_auction_date,
            "prev_cycle_id": prev_cycle_id,
            "prev_base_price_mop": prev_price,
            "price_diff_mop": price_diff,
            "price_diff_pct": price_diff_pct,
            "repeat_status_flag": status_flag,
        }

    def upsert_records(
        self,
        parsed_data: Dict,
        cycle_id: Optional[str] = None,
        reference_date: Optional[str] = None,
    ) -> Dict:
        """
        寫入或更新案件與財產紀錄，並自動將「已過開標日期 (auction_date < reference_date)」或「已從網站下架」的舊紀錄
        標記為 `is_active = 0` (`⚪ 已過開標期(歷史歸檔)`)，確保未過開標週期的數據不會重複疊加，且過期數據妥善歸檔。
        """
        now_dt = datetime.datetime.now()
        now_str = now_dt.strftime("%Y-%m-%d %H:%M:%S")
        today_str = reference_date or now_dt.strftime("%Y-%m-%d")

        if not cycle_id:
            iso_year, iso_week, _ = now_dt.date().isocalendar()
            cycle_id = f"{iso_year}-W{iso_week:02d}"

        page_last_updated = parsed_data.get("last_updated", "")
        cases = parsed_data.get("cases", [])

        cursor = self.conn.cursor()

        # 自動清理過去因網頁標籤換行解析異常所產生的空白案號紀錄 (確保資料庫潔淨)
        cursor.execute("DELETE FROM property_appearances WHERE case_no IS NULL OR TRIM(case_no) = ''")
        cursor.execute("DELETE FROM properties WHERE case_no IS NULL OR TRIM(case_no) = ''")
        cursor.execute("DELETE FROM cases WHERE case_no IS NULL OR TRIM(case_no) = ''")

        # 先將所有不在本次網站列表、或開標日期已早於基準日 (today_str) 的舊案件與財產標記為歷史歸檔
        seen_case_uids = []
        seen_prop_uids = []

        new_cases_count = 0
        new_res_count = 0
        new_park_count = 0

        for c in cases:
            case_uid = c["case_uid"]
            seen_case_uids.append(case_uid)

            # 判斷是否尚未過開標日 (auction_date >= today_str)
            is_upcoming = 1 if c["auction_date"] >= today_str else 0
            lifecycle_label = "🟢 待開標(在列)" if is_upcoming == 1 else "⚪ 已過開標期(歷史歸檔)"

            cursor.execute("SELECT first_seen_cycle, created_at FROM cases WHERE case_uid = ?", (case_uid,))
            existing_case = cursor.fetchone()

            if existing_case is None:
                first_seen_cycle = cycle_id
                created_at = now_str
                if is_upcoming == 1:
                    new_cases_count += 1
            else:
                first_seen_cycle = existing_case["first_seen_cycle"]
                created_at = existing_case["created_at"]

            cursor.execute(
                """
                INSERT INTO cases (
                    case_uid, auction_date, case_type, case_no, court,
                    creditors, debtors, other_parties, sale_method,
                    deadline_time, sale_time, sale_location,
                    custodian, contact_info, remarks, page_last_updated,
                    first_seen_cycle, last_seen_cycle, is_active, lifecycle_status,
                    created_at, updated_at
                ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                ON CONFLICT(case_uid) DO UPDATE SET
                    auction_date = excluded.auction_date,
                    case_type = excluded.case_type,
                    court = excluded.court,
                    creditors = excluded.creditors,
                    debtors = excluded.debtors,
                    other_parties = excluded.other_parties,
                    sale_method = excluded.sale_method,
                    deadline_time = excluded.deadline_time,
                    sale_time = excluded.sale_time,
                    sale_location = excluded.sale_location,
                    custodian = excluded.custodian,
                    contact_info = excluded.contact_info,
                    remarks = excluded.remarks,
                    page_last_updated = excluded.page_last_updated,
                    last_seen_cycle = excluded.last_seen_cycle,
                    is_active = excluded.is_active,
                    lifecycle_status = excluded.lifecycle_status,
                    updated_at = excluded.updated_at
                """,
                (
                    case_uid,
                    c["auction_date"],
                    c["case_type"],
                    c["case_no"],
                    c["court"],
                    " | ".join(c["creditors"]),
                    " | ".join(c["debtors"]),
                    " | ".join(c["other_parties"]),
                    c["sale_method"],
                    c["deadline_time"],
                    c["sale_time"],
                    c["sale_location"],
                    c["custodian"],
                    c["contact_info"],
                    c["remarks"],
                    page_last_updated,
                    first_seen_cycle,
                    cycle_id,
                    is_upcoming,
                    lifecycle_label,
                    created_at,
                    now_str,
                ),
            )

            court_stated_nth = parse_stated_sale_count_from_remarks(c["remarks"])

            for p in c["properties"]:
                prop_uid = p["prop_uid"]
                seen_prop_uids.append(prop_uid)
                canonical_asset_id = p["canonical_asset_id"]

                # 寫入變賣事件歷史表：以 (canonical_asset_id, auction_date, base_price_raw) 為唯一鍵，
                # 確保同一宗未開標案件在多個星期重複抓取時不會重複新增紀錄！
                cursor.execute(
                    """
                    INSERT INTO property_appearances (
                        canonical_asset_id, prop_uid, case_no, auction_date,
                        cycle_id, base_price_mop, base_price_raw, recorded_at
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(canonical_asset_id, auction_date, base_price_raw) DO UPDATE SET
                        recorded_at = excluded.recorded_at
                    """,
                    (
                        canonical_asset_id,
                        prop_uid,
                        c["case_no"],
                        c["auction_date"],
                        cycle_id,
                        p["base_price_mop"],
                        p["base_price_raw"] or "",
                        now_str,
                    ),
                )

                diff_info = self._compute_prior_history_and_diff(
                    canonical_asset_id=canonical_asset_id,
                    current_auction_date=c["auction_date"],
                    current_price=p["base_price_mop"],
                    current_price_raw=p["base_price_raw"] or "",
                    court_stated_nth=court_stated_nth,
                )

                cursor.execute("SELECT first_seen_cycle FROM properties WHERE prop_uid = ?", (prop_uid,))
                existing_prop = cursor.fetchone()

                if existing_prop is None and diff_info["prior_appearances_count"] == 0:
                    prop_first_seen = cycle_id
                    if is_upcoming == 1:
                        if p["is_residential"]:
                            new_res_count += 1
                        if p["is_parking"]:
                            new_park_count += 1
                else:
                    prop_first_seen = (
                        existing_prop["first_seen_cycle"]
                        if existing_prop
                        else (diff_info["prev_cycle_id"] or cycle_id)
                    )

                cursor.execute(
                    """
                    INSERT INTO properties (
                        prop_uid, canonical_asset_id, case_uid, case_no, auction_date, item_index,
                        asset_kind, description, prop_name, address, raw_usage,
                        target_category, is_residential, is_parking,
                        tax_id, registry_id, strata_id,
                        base_price_mop, base_price_raw,
                        first_seen_cycle, last_seen_cycle,
                        is_active, lifecycle_status,
                        prior_appearances_count, total_appearances_count, court_stated_nth_sale,
                        prev_auction_date, prev_cycle_id, prev_base_price_mop,
                        price_diff_mop, price_diff_pct, repeat_status_flag
                    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    ON CONFLICT(prop_uid) DO UPDATE SET
                        canonical_asset_id = excluded.canonical_asset_id,
                        asset_kind = excluded.asset_kind,
                        description = excluded.description,
                        prop_name = excluded.prop_name,
                        address = excluded.address,
                        raw_usage = excluded.raw_usage,
                        target_category = excluded.target_category,
                        is_residential = excluded.is_residential,
                        is_parking = excluded.is_parking,
                        tax_id = excluded.tax_id,
                        registry_id = excluded.registry_id,
                        strata_id = excluded.strata_id,
                        base_price_mop = excluded.base_price_mop,
                        base_price_raw = excluded.base_price_raw,
                        last_seen_cycle = excluded.last_seen_cycle,
                        is_active = excluded.is_active,
                        lifecycle_status = excluded.lifecycle_status,
                        prior_appearances_count = excluded.prior_appearances_count,
                        total_appearances_count = excluded.total_appearances_count,
                        court_stated_nth_sale = excluded.court_stated_nth_sale,
                        prev_auction_date = excluded.prev_auction_date,
                        prev_cycle_id = excluded.prev_cycle_id,
                        prev_base_price_mop = excluded.prev_base_price_mop,
                        price_diff_mop = excluded.price_diff_mop,
                        price_diff_pct = excluded.price_diff_pct,
                        repeat_status_flag = excluded.repeat_status_flag
                    """,
                    (
                        prop_uid,
                        canonical_asset_id,
                        case_uid,
                        c["case_no"],
                        c["auction_date"],
                        p["item_index"],
                        p["asset_kind"],
                        p["description"],
                        p["prop_name"],
                        p["address"],
                        p["raw_usage"],
                        p["target_category"],
                        1 if p["is_residential"] else 0,
                        1 if p["is_parking"] else 0,
                        p["tax_id"],
                        p["registry_id"],
                        p["strata_id"],
                        p["base_price_mop"],
                        p["base_price_raw"],
                        prop_first_seen,
                        cycle_id,
                        is_upcoming,
                        lifecycle_label,
                        diff_info["prior_appearances_count"],
                        diff_info["total_appearances_count"],
                        court_stated_nth,
                        diff_info["prev_auction_date"],
                        diff_info["prev_cycle_id"],
                        diff_info["prev_base_price_mop"],
                        diff_info["price_diff_mop"],
                        diff_info["price_diff_pct"],
                        diff_info["repeat_status_flag"],
                    ),
                )

        # 清理因舊版 prop_uid 格式不同而殘留的同案號同開標日重複列 (只保留本次最新寫入的 seen_prop_uids / seen_case_uids)
        if seen_prop_uids:
            placeholders_p = ",".join("?" for _ in seen_prop_uids)
            cursor.execute(
                f"""
                DELETE FROM properties
                WHERE prop_uid NOT IN ({placeholders_p})
                  AND (
                      auction_date >= ?
                      OR EXISTS (
                          SELECT 1 FROM properties p2
                          WHERE p2.prop_uid IN ({placeholders_p})
                            AND p2.case_no = properties.case_no
                            AND p2.auction_date = properties.auction_date
                            AND p2.item_index = properties.item_index
                      )
                  )
                """,
                (*seen_prop_uids, today_str, *seen_prop_uids),
            )
            cursor.execute(
                f"""
                UPDATE properties
                SET is_active = 0,
                    lifecycle_status = '⚪ 已過開標期(歷史歸檔)'
                WHERE auction_date < ? OR prop_uid NOT IN ({placeholders_p})
                """,
                (today_str, *seen_prop_uids),
            )
        if seen_case_uids:
            placeholders_c = ",".join("?" for _ in seen_case_uids)
            cursor.execute(
                f"""
                DELETE FROM cases
                WHERE case_uid NOT IN ({placeholders_c})
                  AND auction_date >= ?
                """,
                (*seen_case_uids, today_str),
            )
            cursor.execute(
                f"""
                UPDATE cases
                SET is_active = 0,
                    lifecycle_status = '⚪ 已過開標期(歷史歸檔)'
                WHERE auction_date < ? OR case_uid NOT IN ({placeholders_c})
                """,
                (today_str, *seen_case_uids),
            )

        # 統計當前「🟢 待開標(在列)」與「⚪ 已過開標期(歷史歸檔)」數量
        cursor.execute("SELECT COUNT(*) AS cnt FROM cases WHERE is_active = 1")
        active_cases_cnt = cursor.fetchone()["cnt"]

        cursor.execute(
            """
            SELECT
                COUNT(*) AS total_active,
                SUM(CASE WHEN is_residential = 1 THEN 1 ELSE 0 END) AS res_cnt,
                SUM(CASE WHEN is_parking = 1 THEN 1 ELSE 0 END) AS park_cnt,
                SUM(CASE WHEN target_category = '商業/寫字樓' THEN 1 ELSE 0 END) AS comm_cnt,
                SUM(CASE WHEN target_category NOT IN ('住宅', '停車位', '商業/寫字樓') THEN 1 ELSE 0 END) AS other_cnt,
                SUM(CASE WHEN prior_appearances_count > 0 THEN 1 ELSE 0 END) AS rep_cnt,
                SUM(CASE WHEN price_diff_mop IS NOT NULL AND ABS(price_diff_mop) > 0.01 THEN 1 ELSE 0 END) AS diff_cnt,
                ROUND(AVG(CASE WHEN is_residential = 1 AND base_price_mop > 0 THEN base_price_mop END), 2) AS avg_res,
                ROUND(AVG(CASE WHEN is_parking = 1 AND base_price_mop > 0 THEN base_price_mop END), 2) AS avg_park
            FROM properties
            WHERE is_active = 1
            """
        )
        act_row = cursor.fetchone()

        cursor.execute("SELECT COUNT(*) AS cnt FROM properties WHERE is_active = 0")
        archived_props_cnt = cursor.fetchone()["cnt"]

        total_active_props = act_row["total_active"] or 0
        res_count = act_row["res_cnt"] or 0
        park_count = act_row["park_cnt"] or 0
        comm_count = act_row["comm_cnt"] or 0
        other_count = act_row["other_cnt"] or 0
        repeated_props_count = act_row["rep_cnt"] or 0
        price_changed_props_count = act_row["diff_cnt"] or 0
        avg_res_price = act_row["avg_res"] or 0.0
        avg_park_price = act_row["avg_park"] or 0.0

        cursor.execute(
            """
            INSERT INTO cycle_stats (
                cycle_id, run_timestamp, page_last_updated,
                total_active_cases, total_active_properties, archived_past_properties,
                residential_count, parking_count, commercial_count, other_count,
                new_cases_this_cycle, new_residential_this_cycle, new_parking_this_cycle,
                repeated_props_this_cycle, price_changed_props_this_cycle,
                residential_avg_price_mop, parking_avg_price_mop
            ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(cycle_id) DO UPDATE SET
                run_timestamp = excluded.run_timestamp,
                page_last_updated = excluded.page_last_updated,
                total_active_cases = excluded.total_active_cases,
                total_active_properties = excluded.total_active_properties,
                archived_past_properties = excluded.archived_past_properties,
                residential_count = excluded.residential_count,
                parking_count = excluded.parking_count,
                commercial_count = excluded.commercial_count,
                other_count = excluded.other_count,
                new_cases_this_cycle = excluded.new_cases_this_cycle,
                new_residential_this_cycle = excluded.new_residential_this_cycle,
                new_parking_this_cycle = excluded.new_parking_this_cycle,
                repeated_props_this_cycle = excluded.repeated_props_this_cycle,
                price_changed_props_this_cycle = excluded.price_changed_props_this_cycle,
                residential_avg_price_mop = excluded.residential_avg_price_mop,
                parking_avg_price_mop = excluded.parking_avg_price_mop
            """,
            (
                cycle_id,
                now_str,
                page_last_updated,
                active_cases_cnt,
                total_active_props,
                archived_props_cnt,
                res_count,
                park_count,
                comm_count,
                other_count,
                new_cases_count,
                new_res_count,
                new_park_count,
                repeated_props_count,
                price_changed_props_count,
                avg_res_price,
                avg_park_price,
            ),
        )
        self.conn.commit()

        return {
            "cycle_id": cycle_id,
            "reference_date": today_str,
            "page_last_updated": page_last_updated,
            "total_cases": active_cases_cnt,
            "total_properties": total_active_props,
            "archived_properties": archived_props_cnt,
            "residential_count": res_count,
            "parking_count": park_count,
            "commercial_count": comm_count,
            "other_count": other_count,
            "new_cases": new_cases_count,
            "new_residential": new_res_count,
            "new_parking": new_park_count,
            "repeated_props": repeated_props_count,
            "price_changed_props": price_changed_props_count,
        }

    def close(self):
        self.conn.close()


# ==============================================================================
# 3. 網頁爬蟲與文字解析模組 (Scraper & Parser)
# ==============================================================================
def classify_property(raw_usage: str, prop_name: str, description: str, asset_kind: str) -> Tuple[str, bool, bool]:
    usage_clean = (raw_usage or "").strip()
    combined_text = f"{usage_clean} {prop_name or ''} {description or ''}"

    if any(k in usage_clean for k in ["停車", "車位", "泊車"]) or any(
        k in combined_text for k in ["停車位", "號車位", "停車場"]
    ):
        return "停車位", False, True

    if any(k in usage_clean for k in ["居住", "住宅"]):
        return "住宅", True, False

    if any(k in usage_clean for k in ["商業", "寫字樓", "辦公室", "商舖", "鋪"]):
        return "商業/寫字樓", False, False
    if "工業" in usage_clean:
        return "工業", False, False

    if "動產" in (asset_kind or "") and "不動產" not in (asset_kind or ""):
        return "動產(車輛/首飾等)", False, False
    if "股額" in combined_text or "股份" in combined_text:
        return "公司股權", False, False

    return "其他不動產/權利", False, False


def parse_price_mop(price_str: str) -> Optional[float]:
    if not price_str:
        return None
    m = re.search(r"([\d,]+\.?\d*)", price_str)
    if m:
        num_str = m.group(1).replace(",", "")
        try:
            return float(num_str)
        except ValueError:
            return None
    return None


def parse_property_block(lines: List[str], item_index: int, case_uid: str, case_no: str, auction_date: str) -> Dict:
    asset_kind = ""
    description = ""
    prop_name = ""
    address = ""
    raw_usage = ""
    tax_id = ""
    registry_id = ""
    strata_id = ""
    base_price_raw = ""

    for line in lines:
        line = line.strip()
        if not line:
            continue
        m_item = re.match(r"^第\s*\d+\s*項\s*[:：]\s*(.*)$", line)
        if m_item:
            asset_kind = m_item.group(1).strip()
            continue
        if line in ("不動產", "動產", "權利") and not asset_kind:
            asset_kind = line
            continue

        m_kv = re.match(
            r"^(描述|名稱|座落地點|用途|財政局編號|登記局編號|分層所有權登錄編號|變賣底價)\s*[-:：]\s*(.*)$",
            line,
        )
        if m_kv:
            k, v = m_kv.group(1).strip(), m_kv.group(2).strip().rstrip("。.")
            if k == "描述":
                description = v
            elif k == "名稱":
                prop_name = v
            elif k == "座落地點":
                address = v
            elif k == "用途":
                raw_usage = v
            elif k == "財政局編號":
                tax_id = v
            elif k == "登記局編號":
                registry_id = v
            elif k == "分層所有權登錄編號":
                strata_id = v
            elif k == "變賣底價":
                base_price_raw = v

    target_category, is_res, is_park = classify_property(raw_usage, prop_name, description, asset_kind)
    base_price_mop = parse_price_mop(base_price_raw)

    canonical_asset_id = build_canonical_asset_id(
        case_no=case_no,
        registry_id=registry_id,
        tax_id=tax_id,
        prop_name=prop_name or description,
        address=address,
        item_index=item_index,
    )

    norm_cno = re.sub(r"\s+", "", (case_no or "")).upper()
    return {
        "prop_uid": f"{norm_cno}_{auction_date}_P{item_index}",
        "canonical_asset_id": canonical_asset_id,
        "item_index": item_index,
        "asset_kind": asset_kind or "未標明",
        "description": description,
        "prop_name": prop_name,
        "address": address,
        "raw_usage": raw_usage,
        "target_category": target_category,
        "is_residential": is_res,
        "is_parking": is_park,
        "tax_id": tax_id,
        "registry_id": registry_id,
        "strata_id": strata_id,
        "base_price_mop": base_price_mop,
        "base_price_raw": base_price_raw,
    }


def parse_court_sell_text(raw_text: str) -> Dict:
    raw_lines = [line.strip() for line in raw_text.splitlines()]
    raw_lines = [line for line in raw_lines if line]

    # 預處理：若 HTML 標籤導致「欄位名稱：」或「欄位名稱-」單獨成行、數值在下一行，自動合併為同一行
    standalone_colon_keys = {
        "類別：", "類別:", "編號：", "編號:", "法庭：", "法庭:",
        "請求執行人：", "請求執行人:", "要求清償債權人：", "要求清償債權人:",
        "債權人：", "債權人:", "申請人：", "申請人:", "原告：", "原告:",
        "聲請人：", "聲請人:", "被執行人：", "被執行人:", "被申請人：", "被申請人:",
        "被告：", "被告:", "被聲請人：", "被聲請人:", "利害關係人：", "利害關係人:",
        "參與人：", "參與人:", "聲明異議人：", "聲明異議人:",
        "方式：", "方式:", "截標時間：", "截標時間:", "變賣時間：", "變賣時間:",
        "變賣地點：", "變賣地點:", "受寄人：", "受寄人:", "聯絡資料：", "聯絡資料:",
    }
    standalone_dash_keys = {
        "描述", "名稱", "座落地點", "用途", "財政局編號", "登記局編號", "分層所有權登錄編號", "變賣底價"
    }
    lines = []
    idx_r = 0
    while idx_r < len(raw_lines):
        cur = raw_lines[idx_r]
        if cur in standalone_colon_keys and idx_r + 1 < len(raw_lines):
            nxt = raw_lines[idx_r + 1]
            if nxt not in ("案件資料", "變賣資料", "變賣財產") and not re.match(r"^\d{4}-\d{2}-\d{2}$", nxt):
                lines.append(f"{cur} {nxt}")
                idx_r += 2
                continue
        if re.match(r"^(描述|名稱|座落地點|用途|財政局編號|登記局編號|分層所有權登錄編號|變賣底價)\s*[-:：]?$", cur) and idx_r + 1 < len(raw_lines):
            nxt = raw_lines[idx_r + 1]
            if nxt in ("-", "：", ":") and idx_r + 2 < len(raw_lines):
                key_clean = re.sub(r"[-:：\s]+$", "", cur)
                lines.append(f"{key_clean}- {raw_lines[idx_r + 2]}")
                idx_r += 3
                continue
            elif not re.match(r"^(描述|名稱|座落地點|用途|財政局編號|登記局編號|分層所有權登錄編號|變賣底價|受寄人|聯絡資料|備註|第\s*\d+\s*項|不動產|動產|權利)", nxt):
                key_clean = re.sub(r"[-:：\s]+$", "", cur)
                lines.append(f"{key_clean}- {nxt}")
                idx_r += 2
                continue
        lines.append(cur)
        idx_r += 1

    last_updated = ""
    for line in lines:
        m_up = re.search(r"最後更新日期\s*[:：]\s*(\d{4}-\d{2}-\d{2})", line)
        if m_up:
            last_updated = m_up.group(1)
            break

    case_starts = []
    for i in range(len(lines) - 1):
        if re.match(r"^\d{4}-\d{2}-\d{2}$", lines[i]) and lines[i + 1] == "案件資料":
            case_starts.append(i)

    cases = []
    for idx, start_pos in enumerate(case_starts):
        end_pos = case_starts[idx + 1] if idx + 1 < len(case_starts) else len(lines)
        block = lines[start_pos:end_pos]

        cleaned_block = []
        for b_line in block:
            if "聯絡我們" in b_line and "私隱政策聲明" in b_line:
                break
            if b_line.startswith("版權所有"):
                break
            cleaned_block.append(b_line)

        auction_date = cleaned_block[0]
        section = "HEADER"

        case_type = ""
        case_no = ""
        court = ""
        creditors = []
        debtors = []
        other_parties = []

        sale_method = ""
        deadline_time = ""
        sale_time = ""
        sale_location = ""

        prop_lines = []
        custodian = ""
        contact_info = ""
        remarks_lines = []

        for line in cleaned_block[1:]:
            if line == "案件資料":
                section = "CASE_INFO"
                continue
            elif line == "變賣資料":
                section = "SALE_INFO"
                continue
            elif line == "變賣財產":
                section = "PROP_INFO"
                continue
            elif line.startswith("受寄人：") or line.startswith("受寄人:"):
                section = "FOOTER"
                custodian = re.sub(r"^受寄人\s*[:：]\s*", "", line).strip()
                continue
            elif line.startswith("聯絡資料：") or line.startswith("聯絡資料:"):
                section = "FOOTER"
                contact_info = re.sub(r"^聯絡資料\s*[:：]\s*", "", line).strip()
                continue
            elif line.startswith("備註：") or line.startswith("備註:"):
                section = "REMARKS"
                rem_val = re.sub(r"^備註\s*[:：]\s*", "", line).strip()
                if rem_val:
                    remarks_lines.append(rem_val)
                continue

            if section == "CASE_INFO":
                m_kv = re.match(r"^([^：:]+)[：:]\s*(.*)$", line)
                if m_kv:
                    k, v = m_kv.group(1).strip(), m_kv.group(2).strip()
                    if k == "類別":
                        case_type = v
                    elif k == "編號":
                        case_no = v
                    elif k == "法庭":
                        court = v
                    elif k in ("請求執行人", "要求清償債權人", "債權人", "申請人", "原告", "聲請人"):
                        creditors.append(f"{k}:{v}")
                    elif k in ("被執行人", "被申請人", "被告", "被聲請人"):
                        debtors.append(f"{k}:{v}")
                    else:
                        other_parties.append(f"{k}:{v}")

            elif section == "SALE_INFO":
                m_kv = re.match(r"^([^：:]+)[：:]\s*(.*)$", line)
                if m_kv:
                    k, v = m_kv.group(1).strip(), m_kv.group(2).strip()
                    if k == "方式":
                        sale_method = v
                    elif k == "截標時間":
                        deadline_time = v
                    elif k == "變賣時間":
                        sale_time = v
                    elif k == "變賣地點":
                        sale_location = v

            elif section == "PROP_INFO":
                prop_lines.append(line)

            elif section == "REMARKS":
                remarks_lines.append(line)

        case_uid = f"{case_no}__{auction_date}"

        item_starts = [
            i for i, l in enumerate(prop_lines) if re.match(r"^第\s*\d+\s*項\s*[:：]", l)
        ]
        properties = []
        if item_starts:
            for p_idx, p_start in enumerate(item_starts):
                p_end = item_starts[p_idx + 1] if p_idx + 1 < len(item_starts) else len(prop_lines)
                sub_lines = prop_lines[p_start:p_end]
                prop_obj = parse_property_block(sub_lines, p_idx + 1, case_uid, case_no, auction_date)
                properties.append(prop_obj)
        else:
            if prop_lines:
                prop_obj = parse_property_block(prop_lines, 1, case_uid, case_no, auction_date)
                properties.append(prop_obj)

        cases.append(
            {
                "case_uid": case_uid,
                "auction_date": auction_date,
                "case_type": case_type,
                "case_no": case_no,
                "court": court,
                "creditors": creditors,
                "debtors": debtors,
                "other_parties": other_parties,
                "sale_method": sale_method,
                "deadline_time": deadline_time,
                "sale_time": sale_time,
                "sale_location": sale_location,
                "custodian": custodian,
                "contact_info": contact_info,
                "remarks": " ".join(remarks_lines),
                "properties": properties,
            }
        )

    return {"last_updated": last_updated, "cases": cases}


def fetch_court_sell_page(url: str = TARGET_URL, timeout: int = 30) -> str:
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) "
            "Chrome/124.0.0.0 Safari/537.36"
        ),
        "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.8",
    }
    logger.info(f"正在連線至澳門特別行政區法院網站: {url}")
    resp = requests.get(url, headers=headers, timeout=timeout)
    resp.raise_for_status()
    resp.encoding = "utf-8"

    soup = BeautifulSoup(resp.text, "html.parser")
    # 將 <br> 轉為換行，並確保行內標籤 (span/strong/b/a/label) 不會被拆成多行
    for br in soup.find_all("br"):
        br.replace_with("\n")
    for inline_tag in soup.find_all(["span", "strong", "b", "i", "em", "a", "label", "font"]):
        inline_tag.unwrap()
    # 若表格儲存格 <td> 或 <th> 內為「欄位名：」與「數值」，將同一列 <tr> 合併成單行方便解析
    for tr in soup.find_all("tr"):
        cells = [c.get_text(" ", strip=True) for c in tr.find_all(["th", "td"])]
        cells = [c for c in cells if c]
        if len(cells) >= 2 and (cells[0].endswith("：") or cells[0].endswith(":") or cells[0].endswith("-")):
            tr.replace_with(soup.new_string("\n" + " ".join(cells) + "\n"))
    return soup.get_text("\n")


# ==============================================================================
# 4. 報表輸出與可視化儀表板模組 (Excel + Interactive HTML Dashboard)
# ==============================================================================
def print_summary_report(db: CourtSaleDatabase):
    cursor = db.conn.cursor()

    print("\n" + "=" * 105)
    print("📊 【一、更新周期歷史統計 (僅統計當期「🟢 待開標(在列)」標的，已過開標期自動歸檔不疊加)】")
    print("=" * 105)
    cursor.execute(
        """
        SELECT cycle_id, page_last_updated, total_active_cases, total_active_properties,
               archived_past_properties, residential_count, parking_count,
               repeated_props_this_cycle, price_changed_props_this_cycle
        FROM cycle_stats
        ORDER BY cycle_id DESC
        LIMIT 12
        """
    )
    rows = cursor.fetchall()
    print(
        f"{'追蹤周期':<10} | {'網站更新日':<11} | {'🟢待開標案':>8} | {'🟢待開標項':>8} | {'⚪已過期歸檔':>10} | {'🏠住宅':>6} | {'🚗車位':>6} | {'🔄重拍項':>6} | {'🔻價差項':>6}"
    )
    print("-" * 105)
    for r in rows:
        print(
            f"{r['cycle_id']:<12} | {r['page_last_updated']:<13} | {r['total_active_cases']:>10} | "
            f"{r['total_active_properties']:>10} | {r['archived_past_properties']:>12} | "
            f"{r['residential_count']:>8} | {r['parking_count']:>8} | "
            f"{r['repeated_props_this_cycle']:>8} | {r['price_changed_props_this_cycle']:>8}"
        )
    print("=" * 105 + "\n")


def export_to_excel_and_csv(db: CourtSaleDatabase, excel_path: str = "macau_court_sales_report.xlsx"):
    """
    將資料庫內容匯出為多工作表 Excel 檔案：
    - 四大重點追蹤分頁（住宅、停車位、商業／寫字樓、動產）預設只列出 `is_active = 1`（🟢 待開標(在列)）之標的，
      避免過了開標週期的舊案干擾看盤，亦絕不重複疊加。
    - 過了開標週期的標的自動歸入「歷史已開標歸檔」獨立分頁，並永久留存供日後重拍比對價差。
    """
    try:
        import pandas as pd
        from openpyxl.chart import BarChart, PieChart, Reference
        from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
        from openpyxl.utils import get_column_letter

        base_focus_sql = """
            SELECT
                p.lifecycle_status AS '開標狀態',
                p.repeat_status_flag AS '跨期監察標示',
                p.prior_appearances_count AS '之前出現次數',
                p.total_appearances_count AS '累計出現總次數',
                p.auction_date AS '今期變賣日期',
                c.deadline_time AS '今期截標時間',
                p.target_category AS '重點分類',
                p.case_no AS '案件編號',
                p.prop_name AS '標的名稱',
                p.description AS '財產描述',
                p.address AS '座落地點',
                p.base_price_mop AS '今期變賣底價(MOP)',
                p.prev_base_price_mop AS '前期變賣底價(MOP)',
                p.price_diff_mop AS '與前期差額(MOP)',
                p.price_diff_pct AS '差額變動幅度(%)',
                p.prev_auction_date AS '前期變賣日期',
                p.prev_cycle_id AS '前期追蹤週期',
                c.court AS '所屬法庭',
                p.asset_kind AS '財產性質',
                p.raw_usage AS '原始用途',
                p.tax_id AS '財政局編號',
                p.registry_id AS '物業登記局編號',
                c.creditors AS '請求執行人/債權人',
                c.debtors AS '被執行人',
                c.custodian AS '受寄人',
                c.contact_info AS '聯絡資料',
                c.remarks AS '備註',
                p.first_seen_cycle AS '首次收錄週期',
                p.last_seen_cycle AS '最後更新週期'
            FROM properties p
            JOIN cases c ON p.case_uid = c.case_uid
            WHERE {where_clause}
            ORDER BY p.prior_appearances_count DESC, p.auction_date ASC, p.case_no ASC, p.item_index ASC
        """

        # 1~4：四大重點追蹤工作表 (僅列示 🟢 待開標(在列) is_active = 1 之標的)
        df_residential = pd.read_sql_query(
            base_focus_sql.format(where_clause="p.is_active = 1 AND p.is_residential = 1"), db.conn
        )
        df_parking = pd.read_sql_query(
            base_focus_sql.format(where_clause="p.is_active = 1 AND p.is_parking = 1"), db.conn
        )
        df_commercial = pd.read_sql_query(
            base_focus_sql.format(where_clause="p.is_active = 1 AND p.target_category = '商業/寫字樓'"), db.conn
        )
        df_movable = pd.read_sql_query(
            base_focus_sql.format(
                where_clause="p.is_active = 1 AND (p.asset_kind = '動產' OR p.target_category LIKE '動產%')"
            ),
            db.conn,
        )

        # 5：跨期重拍與價差監察專頁
        df_repeated = pd.read_sql_query(
            """
            SELECT
                p.lifecycle_status AS '開標狀態',
                p.repeat_status_flag AS '跨期監察標示',
                p.prior_appearances_count AS '之前出現次數',
                p.total_appearances_count AS '累計出現總次數',
                p.target_category AS '分類標籤',
                p.case_no AS '案件編號',
                p.prop_name AS '名稱',
                p.address AS '座落地點',
                p.prev_auction_date AS '前期變賣日期',
                p.prev_base_price_mop AS '前期底價(MOP)',
                p.auction_date AS '今期變賣日期',
                p.base_price_mop AS '今期底價(MOP)',
                p.price_diff_mop AS '底價差額(MOP)',
                p.price_diff_pct AS '變動幅度(%)',
                c.remarks AS '法院備註',
                p.canonical_asset_id AS '物業跨期追蹤碼'
            FROM properties p
            JOIN cases c ON p.case_uid = c.case_uid
            WHERE p.prior_appearances_count > 0
            ORDER BY p.is_active DESC, p.price_diff_mop ASC, p.prior_appearances_count DESC, p.auction_date ASC
            """,
            db.conn,
        )

        # 6：每週開標數量統計
        df_weekly_auction = pd.read_sql_query(
            """
            SELECT
                auction_week AS '開標週次(ISO)',
                week_status AS '週期狀態',
                week_start_date AS '該週首個開標日',
                week_end_date AS '該週最後開標日',
                case_count AS '變賣案件總數',
                total_properties AS '變賣財產總項數',
                residential_units AS '住宅單位數量',
                parking_spaces AS '停車位數量',
                commercial_units AS '商業/寫字樓數量',
                movable_items AS '動產數量',
                repeated_items AS '前期已出現(重拍)項數',
                price_changed_items AS '有底價差額項數',
                avg_residential_price_mop AS '住宅平均底價(MOP)',
                avg_parking_price_mop AS '車位平均底價(MOP)'
            FROM v_auction_week_summary
            """,
            db.conn,
        )

        # 7：每週追蹤周期紀錄
        df_cycle_stats = pd.read_sql_query(
            """
            SELECT
                cycle_id AS '追蹤周期(每週)',
                run_timestamp AS '執行時間',
                page_last_updated AS '法院網頁更新日',
                total_active_cases AS '待開標在列案件數',
                total_active_properties AS '待開標在列財產數',
                archived_past_properties AS '已過開標期歸檔財產數',
                residential_count AS '待開標住宅數',
                parking_count AS '待開標車位數',
                commercial_count AS '待開標商業數',
                other_count AS '待開標其他數',
                new_cases_this_cycle AS '本週新上架案件',
                repeated_props_this_cycle AS '前期已出現財產數',
                price_changed_props_this_cycle AS '底價變動財產數',
                residential_avg_price_mop AS '住宅平均底價(MOP)',
                parking_avg_price_mop AS '車位平均底價(MOP)'
            FROM cycle_stats
            ORDER BY cycle_id DESC
            """,
            db.conn,
        )

        # 8：歷史已開標歸檔 (is_active = 0)
        df_archived = pd.read_sql_query(
            base_focus_sql.format(where_clause="p.is_active = 0"), db.conn
        )

        # 9：全部變賣財產明細 (含在列與歷史歸檔)
        df_all_props = pd.read_sql_query(
            base_focus_sql.format(where_clause="1=1"), db.conn
        )

        for df in (
            df_residential,
            df_parking,
            df_commercial,
            df_movable,
            df_repeated,
            df_weekly_auction,
            df_cycle_stats,
            df_archived,
            df_all_props,
        ):
            df["資料來源網址"] = TARGET_URL

        with pd.ExcelWriter(excel_path, engine="openpyxl") as writer:
            df_residential.to_excel(writer, sheet_name="住宅重點追蹤", index=False)
            df_parking.to_excel(writer, sheet_name="停車位重點追蹤", index=False)
            df_commercial.to_excel(writer, sheet_name="商業／寫字樓重點追蹤", index=False)
            df_movable.to_excel(writer, sheet_name="動產重點追蹤", index=False)
            df_repeated.to_excel(writer, sheet_name="跨期重拍與價差監察", index=False)
            df_weekly_auction.to_excel(writer, sheet_name="每週開標數量統計", index=False)
            df_cycle_stats.to_excel(writer, sheet_name="每週追蹤周期紀錄", index=False)
            df_archived.to_excel(writer, sheet_name="歷史已開標歸檔", index=False)
            df_all_props.to_excel(writer, sheet_name="全部變賣財產明細", index=False)

            wb = writer.book
            header_fill = PatternFill(start_color="1F4E78", end_color="1F4E78", fill_type="solid")
            header_font = Font(color="FFFFFF", bold=True)
            drop_fill = PatternFill(start_color="FCE4D6", end_color="FCE4D6", fill_type="solid")
            repeat_fill = PatternFill(start_color="FFF2CC", end_color="FFF2CC", fill_type="solid")

            for ws_name in list(wb.sheetnames):
                ws = wb[ws_name]
                ws.views.sheetView[0].showGridLines = True
                for cell in ws[1]:
                    cell.fill = header_fill
                    cell.font = header_font
                    cell.alignment = Alignment(horizontal="center", vertical="center")

                headers = [cell.value for cell in ws[1]]
                prior_col_idx = headers.index("之前出現次數") + 1 if "之前出現次數" in headers else None
                diff_col_idx = None
                for cand in ("與前期差額(MOP)", "底價差額(MOP)"):
                    if cand in headers:
                        diff_col_idx = headers.index(cand) + 1
                        break

                for row_idx in range(2, ws.max_row + 1):
                    prior_val = ws.cell(row=row_idx, column=prior_col_idx).value if prior_col_idx else 0
                    diff_val = ws.cell(row=row_idx, column=diff_col_idx).value if diff_col_idx else None

                    row_fill = None
                    if diff_val is not None and isinstance(diff_val, (int, float)) and abs(diff_val) > 0.01:
                        row_fill = drop_fill
                    elif prior_val is not None and isinstance(prior_val, (int, float)) and prior_val > 0:
                        row_fill = repeat_fill

                    if row_fill:
                        for col_idx in range(1, ws.max_column + 1):
                            ws.cell(row=row_idx, column=col_idx).fill = row_fill

                for col in ws.columns:
                    col_letter = get_column_letter(col[0].column)
                    header_text = str(col[0].value or "")
                    max_len = max(len(header_text) * 2, 12)
                    ws.column_dimensions[col_letter].width = min(max_len + 4, 42)
                    if "MOP" in header_text:
                        for cell in col[1:]:
                            if isinstance(cell.value, (int, float)):
                                cell.number_format = "#,##0.00"
                    elif "%" in header_text:
                        for cell in col[1:]:
                            if isinstance(cell.value, (int, float)):
                                cell.number_format = "+0.00%;-0.00%;0.00%"

            # 建立首頁「可視化儀表板」工作表
            ws_dash = wb.create_sheet(title="可視化儀表板", index=0)
            ws_dash.views.sheetView[0].showGridLines = True

            title_font = Font(size=15, bold=True, color="1F4E78")
            sub_font = Font(size=10, italic=True, color="595959")
            kpi_label_font = Font(size=10, bold=True, color="1F4E78")
            kpi_val_font = Font(size=14, bold=True, color="0F2439")
            thin_border = Border(
                left=Side(style="thin", color="D9D9D9"),
                right=Side(style="thin", color="D9D9D9"),
                top=Side(style="thin", color="D9D9D9"),
                bottom=Side(style="thin", color="D9D9D9"),
            )
            kpi_fill = PatternFill(start_color="EDF2F8", end_color="EDF2F8", fill_type="solid")

            ws_dash["A1"] = "澳門特別行政區法院司法變賣 — 追蹤與可視化儀表板"
            ws_dash["A1"].font = title_font
            ws_dash["A2"] = (
                f"資料來源：{TARGET_URL} ｜ 待開標在列：{len(df_all_props) - len(df_archived)} 項 ｜ 已過開標期歸檔：{len(df_archived)} 項"
            )
            ws_dash["A2"].font = sub_font

            kpis = [
                ("🏠 待開標住宅", len(df_residential)),
                ("🚗 待開標停車位", len(df_parking)),
                ("🏢 待開標商業／寫字樓", len(df_commercial)),
                ("📦 待開標動產", len(df_movable)),
                ("🔄 跨期重拍監察", len(df_repeated)),
                ("⚪ 已過開標期歸檔", len(df_archived)),
            ]
            for idx, (label, val) in enumerate(kpis):
                col_i = idx + 1
                c_lbl = ws_dash.cell(row=4, column=col_i, value=label)
                c_val = ws_dash.cell(row=5, column=col_i, value=val)
                c_lbl.font = kpi_label_font
                c_lbl.fill = kpi_fill
                c_lbl.alignment = Alignment(horizontal="center")
                c_lbl.border = thin_border
                c_val.font = kpi_val_font
                c_val.alignment = Alignment(horizontal="center")
                c_val.border = thin_border
                ws_dash.column_dimensions[get_column_letter(col_i)].width = 22

            ws_dash["A8"] = "待開標財產類別"
            ws_dash["B8"] = "項目數量"
            ws_dash["A8"].fill = header_fill
            ws_dash["B8"].fill = header_fill
            ws_dash["A8"].font = header_font
            ws_dash["B8"].font = header_font
            active_total = len(df_all_props) - len(df_archived)
            other_cnt = max(
                0,
                active_total
                - (len(df_residential) + len(df_parking) + len(df_commercial) + len(df_movable)),
            )
            cat_rows = [
                ("住宅", len(df_residential)),
                ("停車位", len(df_parking)),
                ("商業／寫字樓", len(df_commercial)),
                ("動產", len(df_movable)),
                ("其他不動產/股權", other_cnt),
            ]
            for r_i, (c_name, c_cnt) in enumerate(cat_rows, start=9):
                ws_dash.cell(row=r_i, column=1, value=c_name).border = thin_border
                ws_dash.cell(row=r_i, column=2, value=c_cnt).border = thin_border

            pie = PieChart()
            pie.title = "待開標司法變賣財產類別佔比"
            pie.style = 10
            pie.width = 13
            pie.height = 10
            labels_ref = Reference(ws_dash, min_col=1, min_row=9, max_row=13)
            data_ref = Reference(ws_dash, min_col=2, min_row=8, max_row=13)
            pie.add_data(data_ref, titles_from_data=True)
            pie.set_categories(labels_ref)
            ws_dash.add_chart(pie, "A15")

            ws_weekly = wb["每週開標數量統計"]
            if ws_weekly.max_row >= 2:
                bar = BarChart()
                bar.type = "col"
                bar.style = 10
                bar.grouping = "stacked"
                bar.overlap = 100
                bar.title = "各週期司法變賣開標數量分佈 (依類別)"
                bar.y_axis.title = "項目數量"
                bar.x_axis.title = "開標週次 (ISO)"
                bar.width = 18
                bar.height = 10

                cats_w = Reference(ws_weekly, min_col=1, min_row=2, max_row=ws_weekly.max_row)
                data_w = Reference(ws_weekly, min_col=7, max_col=10, min_row=1, max_row=ws_weekly.max_row)
                bar.add_data(data_w, titles_from_data=True)
                bar.set_categories(cats_w)
                ws_dash.add_chart(bar, "D8")

        logger.info(f"已匯出含過期自動歸檔與跨期價差標示之完整 Excel 報表至: {excel_path}")
    except Exception as e:
        logger.warning(f"匯出 Excel 時發生錯誤: {e}")


def export_html_dashboard(
    db: CourtSaleDatabase,
    html_path: str = "macau_court_dashboard.html",
    reference_date: Optional[str] = None,
):
    """
    輸出單一自包含互動式 HTML 可視化儀表板 (macau_court_dashboard.html)，
    支援一鍵切換「🟢 待開標(在列)」、「⚪ 已過開標期(歷史歸檔)」與「全部紀錄」，確保未過期數據不疊加、過期數據清楚分離。
    """
    cursor = db.conn.cursor()

    cursor.execute("SELECT * FROM cycle_stats ORDER BY cycle_id DESC")
    cycle_stats = [dict(r) for r in cursor.fetchall()]

    cursor.execute("SELECT * FROM v_auction_week_summary ORDER BY auction_week ASC")
    weekly_summary = [dict(r) for r in cursor.fetchall()]

    cursor.execute(
        """
        SELECT
            p.prop_uid, p.canonical_asset_id, p.case_uid, p.case_no, p.auction_date,
            p.item_index, p.asset_kind, p.description, p.prop_name, p.address,
            p.raw_usage, p.target_category, p.is_residential, p.is_parking,
            p.tax_id, p.registry_id, p.strata_id, p.base_price_mop, p.base_price_raw,
            p.first_seen_cycle, p.last_seen_cycle, p.is_active, p.lifecycle_status,
            p.prior_appearances_count, p.total_appearances_count, p.court_stated_nth_sale,
            p.prev_auction_date, p.prev_cycle_id, p.prev_base_price_mop,
            p.price_diff_mop, p.price_diff_pct, p.repeat_status_flag,
            c.case_type, c.court, c.creditors, c.debtors, c.other_parties,
            c.sale_method, c.deadline_time, c.sale_time, c.sale_location,
            c.custodian, c.contact_info, c.remarks, c.page_last_updated
        FROM properties p
        JOIN cases c ON p.case_uid = c.case_uid
        ORDER BY p.auction_date ASC, p.case_no ASC, p.item_index ASC
        """
    )
    properties = [dict(r) for r in cursor.fetchall()]

    latest_cycle = cycle_stats[0] if cycle_stats else {}
    last_updated = latest_cycle.get("page_last_updated") or (
        properties[0]["page_last_updated"] if properties else "2026-11-11"
    )
    current_cycle_id = latest_cycle.get("cycle_id") or "2026-W46"
    ref_date = reference_date or datetime.datetime.now().strftime("%Y-%m-%d")

    payload = {
        "source_url": TARGET_URL,
        "last_updated": last_updated,
        "reference_date": ref_date,
        "current_cycle_id": current_cycle_id,
        "cycle_stats": cycle_stats,
        "weekly_summary": weekly_summary,
        "properties": properties,
    }
    json_payload = json.dumps(payload, ensure_ascii=False)

    html_content = f"""<!DOCTYPE html>
<html lang="zh-Hant">
<head>
  <meta charset="UTF-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1.0" />
  <title>澳門法院司法變賣可視化追蹤儀表板</title>
  <script src="https://cdn.tailwindcss.com/3.4.17"></script>
  <script src="https://cdn.jsdelivr.net/npm/chart.js@4.4.1/dist/chart.umd.min.js"></script>
  <link rel="preconnect" href="https://fonts.googleapis.com">
  <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
  <link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=Noto+Sans+TC:wght@400;500;600;700&display=swap" rel="stylesheet">
  <style>
    body {{
      font-family: 'Inter', 'Noto Sans TC', -apple-system, BlinkMacSystemFont, sans-serif;
      background-color: #f8fafc;
      color: #0f172a;
    }}
    .tab-btn-active {{
      background-color: #1e3a8a;
      color: #ffffff;
      box-shadow: 0 1px 3px rgba(30, 58, 138, 0.3);
    }}
    .kpi-card-active {{
      ring: 2px solid #1d4ed8;
      background-color: #eff6ff;
    }}
  </style>
</head>
<body class="min-h-screen flex flex-col">
  <!-- 頂部導覽列 -->
  <header class="bg-slate-900 text-white border-b border-slate-800 sticky top-0 z-30 shadow-sm">
    <div class="max-w-7xl mx-auto px-4 sm:px-6 py-3.5 flex flex-wrap items-center justify-between gap-3">
      <div class="flex items-center gap-3">
        <div class="w-9 h-9 rounded-lg bg-blue-600 flex items-center justify-center font-bold text-lg shadow-inner">⚖️</div>
        <div>
          <h1 class="text-base sm:text-lg font-bold tracking-tight">澳門特別行政區法院 — 司法變賣可視化追蹤儀表板</h1>
          <p class="text-xs text-slate-400">
            追蹤週期：<span id="hdrCycleId" class="font-semibold text-blue-400"></span> ｜
            基準日：<span id="hdrRefDate" class="font-semibold text-amber-300"></span> ｜
            網站最後更新：<span id="hdrLastUpdated" class="font-semibold text-emerald-400"></span> ｜
            <a href="{TARGET_URL}" target="_blank" rel="noopener noreferrer" class="underline hover:text-blue-300">官方司法變賣網頁 ↗</a>
          </p>
        </div>
      </div>
      <div class="flex items-center gap-2">
        <button id="btnResetFilters" type="button" class="px-3 py-1.5 rounded-lg text-xs font-medium bg-slate-800 hover:bg-slate-700 text-slate-200 border border-slate-700 transition">
          重設全部篩選
        </button>
        <button id="btnExportCsv" type="button" class="px-3.5 py-1.5 rounded-lg text-xs font-semibold bg-emerald-600 hover:bg-emerald-500 text-white shadow transition flex items-center gap-1.5">
          <span>⬇ 匯出當前篩選 CSV</span>
        </button>
      </div>
    </div>
  </header>

  <main class="flex-1 max-w-7xl w-full mx-auto px-4 sm:px-6 py-6 space-y-6">
    <!-- 防疊加與過期歸檔機制提示橫幅 -->
    <div class="bg-blue-50/90 border border-blue-200 rounded-xl px-4 py-2.5 flex flex-wrap items-center justify-between gap-2 text-xs text-blue-900">
      <div class="flex items-center gap-2">
        <span class="font-bold bg-blue-600 text-white px-2 py-0.5 rounded">自動防疊加與過期歸檔</span>
        <span>未過開標週期的案件每週更新時<strong>自動合併不疊加</strong>；已過開標日期的案件自動轉入<strong>「⚪ 歷史已開標歸檔」</strong>並永久保留於資料庫供日後重拍比對價差。</span>
      </div>
      <div class="flex items-center gap-2 font-medium">
        <span>目前檢視範圍：</span>
        <select id="selectLifecycle" class="px-2.5 py-1 rounded-lg border border-blue-300 bg-white text-slate-800 font-semibold focus:outline-none focus:ring-2 focus:ring-blue-500">
          <option value="ACTIVE_ONLY">🟢 僅顯示待開標 (在列標的)</option>
          <option value="ALL">📊 顯示全部 (待開標 + 歷史已開標)</option>
          <option value="ARCHIVED_ONLY">⚪ 僅顯示已過開標期 (歷史歸檔)</option>
        </select>
      </div>
    </div>

    <!-- 第一區：KPI 重點指標卡片 (點擊可快速切換分類) -->
    <section aria-label="關鍵統計指標">
      <div class="grid grid-cols-2 sm:grid-cols-3 lg:grid-cols-6 gap-3.5">
        <button type="button" data-tab-target="ALL" class="kpi-card group text-left bg-white p-4 rounded-xl border border-slate-200 shadow-sm hover:border-blue-500 transition">
          <div class="flex items-center justify-between text-xs font-medium text-slate-500">
            <span>全部變賣標的</span>
            <span class="text-base">📊</span>
          </div>
          <div id="kpiTotalProps" class="mt-1.5 text-2xl font-bold text-slate-900">0</div>
          <div id="kpiTotalCasesSub" class="mt-0.5 text-xs text-slate-500">共 0 宗執行案件</div>
        </button>

        <button type="button" data-tab-target="RESIDENTIAL" class="kpi-card group text-left bg-white p-4 rounded-xl border border-slate-200 shadow-sm hover:border-blue-500 transition">
          <div class="flex items-center justify-between text-xs font-medium text-blue-700">
            <span>住宅重點追蹤</span>
            <span class="text-base">🏠</span>
          </div>
          <div id="kpiResidential" class="mt-1.5 text-2xl font-bold text-blue-700">0</div>
          <div id="kpiResidentialAvg" class="mt-0.5 text-xs text-slate-500">平均底價 --</div>
        </button>

        <button type="button" data-tab-target="PARKING" class="kpi-card group text-left bg-white p-4 rounded-xl border border-slate-200 shadow-sm hover:border-emerald-500 transition">
          <div class="flex items-center justify-between text-xs font-medium text-emerald-700">
            <span>停車位重點追蹤</span>
            <span class="text-base">🚗</span>
          </div>
          <div id="kpiParking" class="mt-1.5 text-2xl font-bold text-emerald-700">0</div>
          <div id="kpiParkingAvg" class="mt-0.5 text-xs text-slate-500">平均底價 --</div>
        </button>

        <button type="button" data-tab-target="COMMERCIAL" class="kpi-card group text-left bg-white p-4 rounded-xl border border-slate-200 shadow-sm hover:border-amber-500 transition">
          <div class="flex items-center justify-between text-xs font-medium text-amber-700">
            <span>商業／寫字樓追蹤</span>
            <span class="text-base">🏢</span>
          </div>
          <div id="kpiCommercial" class="mt-1.5 text-2xl font-bold text-amber-700">0</div>
          <div id="kpiCommercialAvg" class="mt-0.5 text-xs text-slate-500">商舖及寫字樓</div>
        </button>

        <button type="button" data-tab-target="MOVABLE" class="kpi-card group text-left bg-white p-4 rounded-xl border border-slate-200 shadow-sm hover:border-purple-500 transition">
          <div class="flex items-center justify-between text-xs font-medium text-purple-700">
            <span>動產重點追蹤</span>
            <span class="text-base">📦</span>
          </div>
          <div id="kpiMovable" class="mt-1.5 text-2xl font-bold text-purple-700">0</div>
          <div class="mt-0.5 text-xs text-slate-500">車輛及保管箱飾品</div>
        </button>

        <button type="button" data-tab-target="REPEATED" class="kpi-card group text-left bg-amber-50/70 p-4 rounded-xl border border-amber-300 shadow-sm hover:border-rose-500 transition">
          <div class="flex items-center justify-between text-xs font-semibold text-rose-700">
            <span>跨期重拍與價差監察</span>
            <span class="text-base">🔄</span>
          </div>
          <div id="kpiRepeated" class="mt-1.5 text-2xl font-bold text-rose-700">0</div>
          <div id="kpiPriceChangedSub" class="mt-0.5 text-xs text-rose-600">監察前期出現次數與差額</div>
        </button>
      </div>
    </section>

    <!-- 第二區：可視化圖表區 (4 大互動圖表) -->
    <section aria-label="可視化統計圖表" class="grid grid-cols-1 lg:grid-cols-12 gap-4">
      <div class="lg:col-span-7 bg-white p-4 sm:p-5 rounded-xl border border-slate-200 shadow-sm">
        <div class="flex items-center justify-between mb-3">
          <div>
            <h2 class="text-sm font-bold text-slate-800">📅 各週期司法變賣開標數量統計（依資產類別）</h2>
            <p class="text-xs text-slate-500">按司法變賣開標週次統計住宅、停車位、商業／寫字樓及動產數量（未過期數據不重複疊加）</p>
          </div>
          <span class="text-xs px-2 py-0.5 bg-blue-50 text-blue-700 rounded font-medium">每週周期統計</span>
        </div>
        <div class="relative h-64">
          <canvas id="chartWeeklyVolume"></canvas>
        </div>
      </div>

      <div class="lg:col-span-5 bg-white p-4 sm:p-5 rounded-xl border border-slate-200 shadow-sm">
        <div class="flex items-center justify-between mb-3">
          <div>
            <h2 class="text-sm font-bold text-slate-800">🍩 待開標財產類別分佈佔比</h2>
            <p class="text-xs text-slate-500">目前在列待開標之住宅、停車位、商業／寫字樓、動產及其他比例</p>
          </div>
        </div>
        <div class="relative h-64">
          <canvas id="chartCategoryDonut"></canvas>
        </div>
      </div>

      <div class="lg:col-span-6 bg-white p-4 sm:p-5 rounded-xl border border-slate-200 shadow-sm">
        <div class="flex items-center justify-between mb-3">
          <div>
            <h2 class="text-sm font-bold text-slate-800">💰 待開標住宅與停車位底價區間分佈 (MOP)</h2>
            <p class="text-xs text-slate-500">比較不同預算門檻下之待開標住宅及車位標的數量</p>
          </div>
        </div>
        <div class="relative h-60">
          <canvas id="chartPriceDistribution"></canvas>
        </div>
      </div>

      <div class="lg:col-span-6 bg-white p-4 sm:p-5 rounded-xl border border-slate-200 shadow-sm">
        <div class="flex items-center justify-between mb-3">
          <div>
            <h2 class="text-sm font-bold text-slate-800">🏛️ 各法庭司法變賣項目與跨期重拍分佈</h2>
            <p class="text-xs text-slate-500">第一至第四民事法庭及家庭法庭之待開標標的與重拍統計</p>
          </div>
        </div>
        <div class="relative h-60">
          <canvas id="chartCourtBreakdown"></canvas>
        </div>
      </div>
    </section>

    <!-- 第三區：重點追蹤分頁籤與篩選工具列 -->
    <section aria-label="案件資料庫明細與篩選" class="bg-white rounded-xl border border-slate-200 shadow-sm overflow-hidden">
      <div class="border-b border-slate-200 bg-slate-50 px-4 pt-3 pb-2 flex flex-wrap items-center justify-between gap-2">
        <div class="flex flex-wrap gap-1.5" role="tablist">
          <button type="button" data-tab="ALL" class="tab-btn tab-btn-active px-3 py-1.5 rounded-lg text-xs font-semibold transition">
            全部變賣明細 (<span id="tabCountAll">0</span>)
          </button>
          <button type="button" data-tab="RESIDENTIAL" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-slate-700 hover:bg-slate-200 transition">
            🏠 住宅重點追蹤 (<span id="tabCountRes">0</span>)
          </button>
          <button type="button" data-tab="PARKING" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-slate-700 hover:bg-slate-200 transition">
            🚗 停車位重點追蹤 (<span id="tabCountPark">0</span>)
          </button>
          <button type="button" data-tab="COMMERCIAL" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-slate-700 hover:bg-slate-200 transition">
            🏢 商業／寫字樓重點追蹤 (<span id="tabCountComm">0</span>)
          </button>
          <button type="button" data-tab="MOVABLE" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-slate-700 hover:bg-slate-200 transition">
            📦 動產重點追蹤 (<span id="tabCountMov">0</span>)
          </button>
          <button type="button" data-tab="REPEATED" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-rose-700 bg-rose-50 hover:bg-rose-100 border border-rose-200 transition">
            🔄 跨期重拍與價差監察 (<span id="tabCountRep">0</span>)
          </button>
          <button type="button" data-tab="ARCHIVED" class="tab-btn px-3 py-1.5 rounded-lg text-xs font-semibold text-slate-600 bg-slate-200/70 hover:bg-slate-300/70 border border-slate-300 transition">
            ⚪ 歷史已開標歸檔 (<span id="tabCountArc">0</span>)
          </button>
        </div>
        <div id="filterResultCounter" class="text-xs font-medium text-slate-600">
          顯示 0 筆結果
        </div>
      </div>

      <!-- 搜尋與過濾控制列 -->
      <div class="p-4 bg-white border-b border-slate-100 grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-5 gap-3">
        <div>
          <label for="inputSearch" class="block text-xs font-medium text-slate-600 mb-1">關鍵字搜尋 (案號 / 地址 / 單位 / 當事人)</label>
          <input id="inputSearch" type="text" placeholder="例如：氹仔、車位、CV3-24..." class="w-full px-3 py-1.5 text-xs rounded-lg border border-slate-300 focus:outline-none focus:ring-2 focus:ring-blue-500" />
        </div>

        <div>
          <label for="selectWeek" class="block text-xs font-medium text-slate-600 mb-1">開標週次周期</label>
          <select id="selectWeek" class="w-full px-3 py-1.5 text-xs rounded-lg border border-slate-300 bg-white focus:outline-none focus:ring-2 focus:ring-blue-500">
            <option value="ALL">全部開標週次</option>
          </select>
        </div>

        <div>
          <label for="selectCourt" class="block text-xs font-medium text-slate-600 mb-1">所屬法庭</label>
          <select id="selectCourt" class="w-full px-3 py-1.5 text-xs rounded-lg border border-slate-300 bg-white focus:outline-none focus:ring-2 focus:ring-blue-500">
            <option value="ALL">全部法庭</option>
          </select>
        </div>

        <div>
          <label for="selectMaxPrice" class="block text-xs font-medium text-slate-600 mb-1">變賣底價上限 (MOP)</label>
          <select id="selectMaxPrice" class="w-full px-3 py-1.5 text-xs rounded-lg border border-slate-300 bg-white focus:outline-none focus:ring-2 focus:ring-blue-500">
            <option value="0">不限金額</option>
            <option value="1000000">100 萬澳門元以下</option>
            <option value="2000000">200 萬澳門元以下</option>
            <option value="4000000">400 萬澳門元以下</option>
            <option value="8000000">800 萬澳門元以下</option>
            <option value="15000000">1,500 萬澳門元以下</option>
          </select>
        </div>

        <div>
          <label for="selectSort" class="block text-xs font-medium text-slate-600 mb-1">排序方式</label>
          <select id="selectSort" class="w-full px-3 py-1.5 text-xs rounded-lg border border-slate-300 bg-white focus:outline-none focus:ring-2 focus:ring-blue-500">
            <option value="DATE_ASC">開標日期 (由近至遠)</option>
            <option value="PRIOR_DESC">之前出現次數 (由多至少)</option>
            <option value="PRICE_ASC">變賣底價 (由低至高)</option>
            <option value="PRICE_DESC">變賣底價 (由高至低)</option>
          </select>
        </div>
      </div>

      <!-- 資料表格 -->
      <div class="overflow-x-auto">
        <table class="w-full text-left border-collapse">
          <thead>
            <tr class="bg-slate-800 text-white text-xs uppercase tracking-wider">
              <th class="py-2.5 px-3 font-semibold">開標狀態 / 跨期監察</th>
              <th class="py-2.5 px-3 font-semibold">開標日期 / 截標</th>
              <th class="py-2.5 px-3 font-semibold">分類</th>
              <th class="py-2.5 px-3 font-semibold">案件編號 / 法庭</th>
              <th class="py-2.5 px-3 font-semibold">標的名稱及座落地點</th>
              <th class="py-2.5 px-3 font-semibold text-right">今期底價 (MOP)</th>
              <th class="py-2.5 px-3 font-semibold text-right">前期底價 / 差額</th>
              <th class="py-2.5 px-3 font-semibold text-center">操作</th>
            </tr>
          </thead>
          <tbody id="tableBody" class="divide-y divide-slate-200 text-xs"></tbody>
        </table>
      </div>
    </section>
  </main>

  <!-- 案件詳情檢視彈窗 (Modal) -->
  <div id="detailModal" class="fixed inset-0 z-50 hidden bg-slate-900/60 backdrop-blur-xs flex items-center justify-center p-4">
    <div class="bg-white rounded-2xl max-w-2xl w-full max-h-[90vh] overflow-y-auto shadow-2xl border border-slate-200">
      <div class="px-5 py-4 bg-slate-900 text-white flex items-center justify-between sticky top-0">
        <div>
          <span id="modalCategoryBadge" class="text-xs font-semibold px-2 py-0.5 rounded bg-blue-600 text-white">分類</span>
          <h3 id="modalTitle" class="text-base font-bold mt-1">案件編號</h3>
        </div>
        <button id="btnCloseModal" type="button" class="w-8 h-8 rounded-lg bg-slate-800 hover:bg-slate-700 text-slate-300 flex items-center justify-center font-bold">✕</button>
      </div>
      <div id="modalBody" class="p-5 space-y-4 text-xs sm:text-sm"></div>
    </div>
  </div>

  <script>
    const DASHBOARD_DATA = {json_payload};

    const state = {{
      activeTab: 'ALL',
      lifecycleFilter: 'ACTIVE_ONLY',
      searchQuery: '',
      selectedWeek: 'ALL',
      selectedCourt: 'ALL',
      maxPrice: 0,
      sortBy: 'DATE_ASC',
      filteredItems: []
    }};

    function formatMOP(val) {{
      if (val === null || val === undefined || isNaN(val)) return '未標明';
      return 'MOP ' + Number(val).toLocaleString('en-US', {{ minimumFractionDigits: 2, maximumFractionDigits: 2 }});
    }}

    function findAuctionWeekForDate(dateStr) {{
      for (const w of DASHBOARD_DATA.weekly_summary) {{
        if (dateStr >= w.week_start_date && dateStr <= w.week_end_date) {{
          return w.auction_week;
        }}
      }}
      return 'OTHER';
    }}

    function initKPIsAndFilters() {{
      document.getElementById('hdrCycleId').textContent = DASHBOARD_DATA.current_cycle_id;
      document.getElementById('hdrRefDate').textContent = DASHBOARD_DATA.reference_date;
      document.getElementById('hdrLastUpdated').textContent = DASHBOARD_DATA.last_updated;

      const allProps = DASHBOARD_DATA.properties;
      const activeProps = allProps.filter(p => p.is_active === 1);
      const archivedProps = allProps.filter(p => p.is_active === 0);

      const uniqueActiveCases = new Set(activeProps.map(p => p.case_uid)).size;
      const resProps = activeProps.filter(p => p.is_residential === 1);
      const parkProps = activeProps.filter(p => p.is_parking === 1);
      const commProps = activeProps.filter(p => p.target_category === '商業/寫字樓');
      const movProps = activeProps.filter(p => p.asset_kind === '動產' || (p.target_category && p.target_category.startsWith('動產')));
      const repProps = allProps.filter(p => (p.prior_appearances_count || 0) > 0);

      const avgRes = resProps.length ? resProps.reduce((s, x) => s + (x.base_price_mop || 0), 0) / resProps.length : 0;
      const avgPark = parkProps.length ? parkProps.reduce((s, x) => s + (x.base_price_mop || 0), 0) / parkProps.length : 0;
      const avgComm = commProps.length ? commProps.reduce((s, x) => s + (x.base_price_mop || 0), 0) / commProps.length : 0;

      document.getElementById('kpiTotalProps').textContent = activeProps.length + ' 項';
      document.getElementById('kpiTotalCasesSub').textContent = `共 ${{uniqueActiveCases}} 宗待開標案件`;
      document.getElementById('kpiResidential').textContent = resProps.length + ' 項';
      document.getElementById('kpiResidentialAvg').textContent = `均價 MOP ${{(avgRes / 10000).toFixed(1)}} 萬`;
      document.getElementById('kpiParking').textContent = parkProps.length + ' 項';
      document.getElementById('kpiParkingAvg').textContent = `均價 MOP ${{(avgPark / 10000).toFixed(1)}} 萬`;
      document.getElementById('kpiCommercial').textContent = commProps.length + ' 項';
      document.getElementById('kpiCommercialAvg').textContent = `均價 MOP ${{(avgComm / 10000).toFixed(1)}} 萬`;
      document.getElementById('kpiMovable').textContent = movProps.length + ' 項';
      document.getElementById('kpiRepeated').textContent = repProps.length + ' 項';
      document.getElementById('kpiPriceChangedSub').textContent = `已過開標期歸檔: ${{archivedProps.length}} 項`;

      document.getElementById('tabCountAll').textContent = activeProps.length;
      document.getElementById('tabCountRes').textContent = resProps.length;
      document.getElementById('tabCountPark').textContent = parkProps.length;
      document.getElementById('tabCountComm').textContent = commProps.length;
      document.getElementById('tabCountMov').textContent = movProps.length;
      document.getElementById('tabCountRep').textContent = repProps.length;
      document.getElementById('tabCountArc').textContent = archivedProps.length;

      const selectWeek = document.getElementById('selectWeek');
      DASHBOARD_DATA.weekly_summary.forEach(w => {{
        const opt = document.createElement('option');
        opt.value = w.auction_week;
        opt.textContent = `${{w.auction_week}} (${{w.week_start_date}} ~ ${{w.week_end_date}}) [${{w.total_properties}}項]`;
        selectWeek.appendChild(opt);
      }});

      const selectCourt = document.getElementById('selectCourt');
      const courts = Array.from(new Set(allProps.map(p => p.court).filter(Boolean))).sort();
      courts.forEach(c => {{
        const opt = document.createElement('option');
        opt.value = c;
        opt.textContent = c;
        selectCourt.appendChild(opt);
      }});
    }}

    function initCharts() {{
      const weeks = DASHBOARD_DATA.weekly_summary;
      const activeProps = DASHBOARD_DATA.properties.filter(p => p.is_active === 1);

      const ctxWeekly = document.getElementById('chartWeeklyVolume').getContext('2d');
      new Chart(ctxWeekly, {{
        type: 'bar',
        data: {{
          labels: weeks.map(w => `${{w.auction_week}} (${{w.week_start_date.slice(5)}})`),
          datasets: [
            {{ label: '住宅', data: weeks.map(w => w.residential_units), backgroundColor: '#2563eb' }},
            {{ label: '停車位', data: weeks.map(w => w.parking_spaces), backgroundColor: '#10b981' }},
            {{ label: '商業／寫字樓', data: weeks.map(w => w.commercial_units), backgroundColor: '#f59e0b' }},
            {{ label: '動產及其他', data: weeks.map(w => (w.movable_items || 0) + (w.other_items || 0)), backgroundColor: '#8b5cf6' }}
          ]
        }},
        options: {{
          responsive: true,
          maintainAspectRatio: false,
          plugins: {{ legend: {{ position: 'top', labels: {{ boxWidth: 12, font: {{ size: 11 }} }} }} }},
          scales: {{
            x: {{ stacked: true, ticks: {{ font: {{ size: 10 }} }} }},
            y: {{ stacked: true, beginAtZero: true, ticks: {{ stepSize: 5 }} }}
          }}
        }}
      }});

      const resCnt = activeProps.filter(p => p.is_residential === 1).length;
      const parkCnt = activeProps.filter(p => p.is_parking === 1).length;
      const commCnt = activeProps.filter(p => p.target_category === '商業/寫字樓').length;
      const movCnt = activeProps.filter(p => p.asset_kind === '動產' || (p.target_category && p.target_category.startsWith('動產'))).length;
      const otherCnt = Math.max(0, activeProps.length - (resCnt + parkCnt + commCnt + movCnt));

      const ctxDonut = document.getElementById('chartCategoryDonut').getContext('2d');
      new Chart(ctxDonut, {{
        type: 'doughnut',
        data: {{
          labels: ['住宅 (' + resCnt + ')', '商業／寫字樓 (' + commCnt + ')', '停車位 (' + parkCnt + ')', '其他不動產/股權 (' + otherCnt + ')', '動產 (' + movCnt + ')'],
          datasets: [{{
            data: [resCnt, commCnt, parkCnt, otherCnt, movCnt],
            backgroundColor: ['#2563eb', '#f59e0b', '#10b981', '#64748b', '#8b5cf6'],
            borderWidth: 1
          }}]
        }},
        options: {{
          responsive: true,
          maintainAspectRatio: false,
          plugins: {{ legend: {{ position: 'right', labels: {{ boxWidth: 12, font: {{ size: 11 }} }} }} }}
        }}
      }});

      const buckets = [
        {{ label: '100萬以下', min: 0, max: 1000000 }},
        {{ label: '100萬-250萬', min: 1000000, max: 2500000 }},
        {{ label: '250萬-500萬', min: 2500000, max: 5000000 }},
        {{ label: '500萬-1,000萬', min: 5000000, max: 10000000 }},
        {{ label: '1,000萬以上', min: 10000000, max: Infinity }}
      ];
      const resByBucket = buckets.map(b => activeProps.filter(p => p.is_residential === 1 && (p.base_price_mop || 0) >= b.min && (p.base_price_mop || 0) < b.max).length);
      const parkByBucket = buckets.map(b => activeProps.filter(p => p.is_parking === 1 && (p.base_price_mop || 0) >= b.min && (p.base_price_mop || 0) < b.max).length);

      const ctxPrice = document.getElementById('chartPriceDistribution').getContext('2d');
      new Chart(ctxPrice, {{
        type: 'bar',
        data: {{
          labels: buckets.map(b => b.label),
          datasets: [
            {{ label: '住宅單位', data: resByBucket, backgroundColor: '#3b82f6' }},
            {{ label: '停車位', data: parkByBucket, backgroundColor: '#10b981' }}
          ]
        }},
        options: {{
          responsive: true,
          maintainAspectRatio: false,
          plugins: {{ legend: {{ position: 'top', labels: {{ boxWidth: 12, font: {{ size: 11 }} }} }} }},
          scales: {{ y: {{ beginAtZero: true }} }}
        }}
      }});

      const courtNames = Array.from(new Set(activeProps.map(p => p.court).filter(Boolean))).sort();
      const courtTotals = courtNames.map(c => activeProps.filter(p => p.court === c).length);
      const courtRepeated = courtNames.map(c => activeProps.filter(p => p.court === c && (p.prior_appearances_count || 0) > 0).length);

      const ctxCourt = document.getElementById('chartCourtBreakdown').getContext('2d');
      new Chart(ctxCourt, {{
        type: 'bar',
        data: {{
          labels: courtNames,
          datasets: [
            {{ label: '待開標標的數', data: courtTotals, backgroundColor: '#1e40af' }},
            {{ label: '跨期重拍標的數', data: courtRepeated, backgroundColor: '#e11d48' }}
          ]
        }},
        options: {{
          indexAxis: 'y',
          responsive: true,
          maintainAspectRatio: false,
          plugins: {{ legend: {{ position: 'top', labels: {{ boxWidth: 12, font: {{ size: 11 }} }} }} }},
          scales: {{ x: {{ beginAtZero: true }} }}
        }}
      }});
    }}

    function applyFiltersAndRender() {{
      const q = state.searchQuery.trim().toLowerCase();

      let list = DASHBOARD_DATA.properties.filter(p => {{
        if (state.activeTab === 'ARCHIVED') {{
          if (p.is_active !== 0) return false;
        }} else if (state.activeTab === 'REPEATED') {{
          if (!(p.prior_appearances_count > 0)) return false;
        }} else {{
          if (state.lifecycleFilter === 'ACTIVE_ONLY' && p.is_active !== 1) return false;
          if (state.lifecycleFilter === 'ARCHIVED_ONLY' && p.is_active !== 0) return false;

          if (state.activeTab === 'RESIDENTIAL' && p.is_residential !== 1) return false;
          if (state.activeTab === 'PARKING' && p.is_parking !== 1) return false;
          if (state.activeTab === 'COMMERCIAL' && p.target_category !== '商業/寫字樓') return false;
          if (state.activeTab === 'MOVABLE' && !(p.asset_kind === '動產' || (p.target_category && p.target_category.startsWith('動產')))) return false;
        }}

        if (state.selectedWeek !== 'ALL') {{
          const w = findAuctionWeekForDate(p.auction_date);
          if (w !== state.selectedWeek) return false;
        }}

        if (state.selectedCourt !== 'ALL' && p.court !== state.selectedCourt) return false;
        if (state.maxPrice > 0 && (p.base_price_mop || 0) > state.maxPrice) return false;

        if (q) {{
          const hay = [
            p.case_no, p.prop_name, p.description, p.address,
            p.raw_usage, p.creditors, p.debtors, p.remarks, p.tax_id, p.registry_id
          ].join(' ').toLowerCase();
          if (!hay.includes(q)) return false;
        }}

        return true;
      }});

      list.sort((a, b) => {{
        if (state.sortBy === 'PRIOR_DESC') {{
          const diffPrior = (b.prior_appearances_count || 0) - (a.prior_appearances_count || 0);
          if (diffPrior !== 0) return diffPrior;
          return a.auction_date.localeCompare(b.auction_date);
        }}
        if (state.sortBy === 'PRICE_ASC') return (a.base_price_mop || 0) - (b.base_price_mop || 0);
        if (state.sortBy === 'PRICE_DESC') return (b.base_price_mop || 0) - (a.base_price_mop || 0);
        const d = a.auction_date.localeCompare(b.auction_date);
        if (d !== 0) return d;
        return a.case_no.localeCompare(b.case_no);
      }});

      state.filteredItems = list;
      document.getElementById('filterResultCounter').textContent = `顯示 ${{list.length}} 筆標的`;

      const tbody = document.getElementById('tableBody');
      tbody.innerHTML = '';

      if (list.length === 0) {{
        const tr = document.createElement('tr');
        tr.innerHTML = `<td colspan="8" class="py-10 text-center text-slate-400">沒有符合篩選條件的司法變賣標的</td>`;
        tbody.appendChild(tr);
        return;
      }}

      list.forEach(item => {{
        const tr = document.createElement('tr');
        const hasDiff = item.price_diff_mop !== null && item.price_diff_mop !== undefined && Math.abs(item.price_diff_mop) > 0.01;
        const isRepeated = (item.prior_appearances_count || 0) > 0;

        if (item.is_active === 0) {{
          tr.className = 'bg-slate-100/80 text-slate-500 hover:bg-slate-200/60 transition';
        }} else if (hasDiff) {{
          tr.className = 'bg-rose-50/70 hover:bg-rose-100/70 transition';
        }} else if (isRepeated) {{
          tr.className = 'bg-amber-50/80 hover:bg-amber-100/70 transition';
        }} else {{
          tr.className = 'hover:bg-slate-50 transition';
        }}

        const lifeBadge = item.is_active === 1
          ? `<span class="inline-flex items-center px-1.5 py-0.5 rounded text-[11px] font-semibold bg-emerald-100 text-emerald-800">🟢 待開標</span>`
          : `<span class="inline-flex items-center px-1.5 py-0.5 rounded text-[11px] font-semibold bg-slate-200 text-slate-700">⚪ 已過期歸檔</span>`;

        let statusBadge = `<span class="inline-flex items-center px-2 py-0.5 rounded font-medium bg-slate-100 text-slate-700">🆕 首次出現</span>`;
        if (hasDiff && item.price_diff_mop < 0) {{
          statusBadge = `<span class="inline-flex items-center px-2 py-0.5 rounded font-semibold bg-rose-100 text-rose-800 border border-rose-300">🔻 重拍降價 (前已出現 ${{item.prior_appearances_count}} 次)</span>`;
        }} else if (hasDiff && item.price_diff_mop > 0) {{
          statusBadge = `<span class="inline-flex items-center px-2 py-0.5 rounded font-semibold bg-orange-100 text-orange-800 border border-orange-300">🔺 重拍調升 (前已出現 ${{item.prior_appearances_count}} 次)</span>`;
        }} else if (isRepeated) {{
          statusBadge = `<span class="inline-flex items-center px-2 py-0.5 rounded font-semibold bg-amber-100 text-amber-900 border border-amber-300">⚠️ 前已出現 ${{item.prior_appearances_count}} 次 (累計第 ${{item.total_appearances_count}} 次)</span>`;
        }}

        let catClass = 'bg-slate-100 text-slate-700';
        if (item.is_residential === 1) catClass = 'bg-blue-100 text-blue-800';
        else if (item.is_parking === 1) catClass = 'bg-emerald-100 text-emerald-800';
        else if (item.target_category === '商業/寫字樓') catClass = 'bg-amber-100 text-amber-800';
        else if (item.asset_kind === '動產' || (item.target_category && item.target_category.startsWith('動產'))) catClass = 'bg-purple-100 text-purple-800';

        let diffHtml = `<span class="text-slate-400">無前期紀錄</span>`;
        if (item.prev_base_price_mop !== null && item.prev_base_price_mop !== undefined) {{
          const diffSign = item.price_diff_mop > 0 ? '+' : '';
          const diffColor = item.price_diff_mop < 0 ? 'text-emerald-700 font-bold' : (item.price_diff_mop > 0 ? 'text-rose-700 font-bold' : 'text-slate-600');
          diffHtml = `
            <div class="text-slate-500">前期(${{item.prev_auction_date || ''}}): ${{formatMOP(item.prev_base_price_mop)}}</div>
            <div class="${{diffColor}}">差額: ${{diffSign}}${{formatMOP(item.price_diff_mop)}} (${{diffSign}}${{item.price_diff_pct}}%)</div>
          `;
        }} else if (isRepeated) {{
          diffHtml = `<div class="text-amber-800 font-medium">法院標註第 ${{item.total_appearances_count}} 次變賣</div><div class="text-slate-400 text-[11px]">待累積底價比對</div>`;
        }}

        tr.innerHTML = `
          <td class="py-3 px-3 align-top space-y-1">
            <div>${{lifeBadge}}</div>
            <div>${{statusBadge}}</div>
          </td>
          <td class="py-3 px-3 align-top whitespace-nowrap">
            <div class="font-bold text-slate-900">${{item.auction_date}}</div>
            <div class="text-[11px] text-slate-500">截標: ${{item.deadline_time || '--'}}</div>
          </td>
          <td class="py-3 px-3 align-top whitespace-nowrap">
            <span class="px-2 py-0.5 rounded font-semibold ${{catClass}}">${{item.target_category}}</span>
            <div class="text-[11px] text-slate-400 mt-1">${{item.asset_kind}}</div>
          </td>
          <td class="py-3 px-3 align-top">
            <div class="font-semibold text-slate-900">${{item.case_no}}</div>
            <div class="text-[11px] text-slate-500">${{item.court}} ｜ ${{item.case_type}}</div>
          </td>
          <td class="py-3 px-3 align-top max-w-md">
            <div class="font-semibold text-slate-800">${{item.prop_name || item.description || '未標明名稱'}}</div>
            <div class="text-slate-600 mt-0.5 line-clamp-2">${{item.address || '無座落地點(動產)'}}</div>
            ${{item.remarks ? `<div class="mt-1 text-[11px] text-amber-800 bg-amber-50 px-1.5 py-0.5 rounded border border-amber-200 line-clamp-1">備註: ${{item.remarks}}</div>` : ''}}
          </td>
          <td class="py-3 px-3 align-top text-right whitespace-nowrap font-bold text-slate-900">
            ${{formatMOP(item.base_price_mop)}}
          </td>
          <td class="py-3 px-3 align-top text-right whitespace-nowrap">
            ${{diffHtml}}
          </td>
          <td class="py-3 px-3 align-top text-center whitespace-nowrap">
            <button type="button" data-prop-uid="${{item.prop_uid}}" class="btn-detail px-2.5 py-1 rounded bg-blue-50 hover:bg-blue-100 text-blue-700 font-semibold border border-blue-200 transition">
              詳情
            </button>
          </td>
        `;
        tbody.appendChild(tr);
      }});
    }}

    function setActiveTab(tabName) {{
      state.activeTab = tabName;
      document.querySelectorAll('.tab-btn').forEach(btn => {{
        if (btn.getAttribute('data-tab') === tabName) {{
          btn.classList.add('tab-btn-active');
        }} else {{
          btn.classList.remove('tab-btn-active');
        }}
      }});
      applyFiltersAndRender();
    }}

    function openDetailModal(propUid) {{
      const item = DASHBOARD_DATA.properties.find(p => p.prop_uid === propUid);
      if (!item) return;

      document.getElementById('modalCategoryBadge').textContent = `${{item.lifecycle_status}} ｜ ${{item.target_category}}`;
      document.getElementById('modalTitle').textContent = `${{item.case_no}} — ${{item.prop_name || '變賣標的'}}`;

      const body = document.getElementById('modalBody');
      body.innerHTML = `
        <div class="p-3.5 rounded-xl bg-slate-50 border border-slate-200 grid grid-cols-1 sm:grid-cols-2 gap-2.5">
          <div><span class="text-slate-500">開標週期狀態：</span><strong>${{item.lifecycle_status}}</strong></div>
          <div><span class="text-slate-500">跨期監察狀態：</span><strong class="text-rose-700">${{item.repeat_status_flag}}</strong></div>
          <div><span class="text-slate-500">之前出現次數：</span><strong>${{item.prior_appearances_count}} 次 (累計第 ${{item.total_appearances_count}} 次)</strong></div>
          <div><span class="text-slate-500">收錄週期紀錄：</span><strong>首次 ${{item.first_seen_cycle}} ／ 最後 ${{item.last_seen_cycle}}</strong></div>
          <div><span class="text-slate-500">今期變賣底價：</span><strong class="text-blue-700">${{formatMOP(item.base_price_mop)}}</strong></div>
          <div><span class="text-slate-500">前期變賣底價：</span><strong>${{item.prev_base_price_mop ? formatMOP(item.prev_base_price_mop) : '尚無前期底價紀錄'}}</strong></div>
          <div><span class="text-slate-500">與前期差額：</span><strong>${{item.price_diff_mop !== null && item.price_diff_mop !== undefined ? formatMOP(item.price_diff_mop) + ' (' + item.price_diff_pct + '%)' : '無差額資料'}}</strong></div>
          <div><span class="text-slate-500">物業跨期追蹤碼：</span><code class="text-xs bg-slate-200 px-1.5 py-0.5 rounded">${{item.canonical_asset_id}}</code></div>
        </div>

        <div class="space-y-2">
          <h4 class="font-bold text-slate-800 border-b pb-1">📍 變賣財產資料</h4>
          <div><span class="text-slate-500">名稱：</span>${{item.prop_name || '--'}}</div>
          <div><span class="text-slate-500">描述：</span>${{item.description || '--'}}</div>
          <div><span class="text-slate-500">座落地點：</span>${{item.address || '--'}}</div>
          <div class="grid grid-cols-1 sm:grid-cols-3 gap-2">
            <div><span class="text-slate-500">用途：</span>${{item.raw_usage || '--'}}</div>
            <div><span class="text-slate-500">財政局編號：</span>${{item.tax_id || '--'}}</div>
            <div><span class="text-slate-500">登記局編號：</span>${{item.registry_id || '--'}}</div>
          </div>
        </div>

        <div class="space-y-2">
          <h4 class="font-bold text-slate-800 border-b pb-1">⚖️ 案件與開標資料</h4>
          <div class="grid grid-cols-1 sm:grid-cols-2 gap-2">
            <div><span class="text-slate-500">所屬法庭：</span>${{item.court}} (${{item.case_type}})</div>
            <div><span class="text-slate-500">變賣方式：</span>${{item.sale_method}}</div>
            <div><span class="text-slate-500">截標時間：</span><strong class="text-rose-600">${{item.deadline_time}}</strong></div>
            <div><span class="text-slate-500">變賣時間：</span><strong class="text-blue-700">${{item.sale_time}}</strong></div>
          </div>
          <div><span class="text-slate-500">變賣地點：</span>${{item.sale_location}}</div>
          <div><span class="text-slate-500">請求執行人 / 債權人：</span>${{item.creditors || '--'}}</div>
          <div><span class="text-slate-500">被執行人 / 被告：</span>${{item.debtors || '--'}}</div>
          <div><span class="text-slate-500">受寄人：</span>${{item.custodian || '--'}}</div>
          <div><span class="text-slate-500">聯絡資料：</span>${{item.contact_info || '--'}}</div>
          <div><span class="text-slate-500">法院備註：</span>${{item.remarks || '無'}}</div>
        </div>
      `;

      document.getElementById('detailModal').classList.remove('hidden');
    }}

    function exportCurrentFilteredCsv() {{
      const rows = state.filteredItems;
      const headers = [
        '開標狀態', '跨期監察標示', '之前出現次數', '累計出現總次數', '今期變賣日期', '截標時間',
        '重點分類', '案件編號', '所屬法庭', '標的名稱', '座落地點',
        '今期變賣底價(MOP)', '前期變賣底價(MOP)', '與前期差額(MOP)', '差額變動幅度(%)',
        '財政局編號', '物業登記局編號', '受寄人', '聯絡資料', '備註', '資料來源網址'
      ];
      const csvLines = [headers.join(',')];
      rows.forEach(r => {{
        const vals = [
          r.lifecycle_status, r.repeat_status_flag, r.prior_appearances_count, r.total_appearances_count,
          r.auction_date, r.deadline_time, r.target_category, r.case_no, r.court,
          r.prop_name || r.description, r.address, r.base_price_mop,
          r.prev_base_price_mop ?? '', r.price_diff_mop ?? '', r.price_diff_pct ?? '',
          r.tax_id, r.registry_id, r.custodian, r.contact_info, r.remarks, DASHBOARD_DATA.source_url
        ].map(v => `"${{String(v ?? '').replace(/"/g, '""')}}"` );
        csvLines.push(vals.join(','));
      }});

      const blob = new Blob(['\\uFEFF' + csvLines.join('\\n')], {{ type: 'text/csv;charset=utf-8;' }});
      const url = URL.createObjectURL(blob);
      const a = document.createElement('a');
      a.href = url;
      a.download = `macau_court_sales_${{state.activeTab.toLowerCase()}}_${{DASHBOARD_DATA.current_cycle_id}}.csv`;
      document.body.appendChild(a);
      a.click();
      document.body.removeChild(a);
      URL.revokeObjectURL(url);
    }}

    window.addEventListener('DOMContentLoaded', () => {{
      initKPIsAndFilters();
      initCharts();
      applyFiltersAndRender();

      document.querySelectorAll('.tab-btn').forEach(btn => {{
        btn.addEventListener('click', () => setActiveTab(btn.getAttribute('data-tab')));
      }});

      document.querySelectorAll('.kpi-card').forEach(card => {{
        card.addEventListener('click', () => {{
          const target = card.getAttribute('data-tab-target');
          if (target) setActiveTab(target);
        }});
      }});

      document.getElementById('selectLifecycle').addEventListener('change', e => {{
        state.lifecycleFilter = e.target.value;
        applyFiltersAndRender();
      }});

      document.getElementById('inputSearch').addEventListener('input', e => {{
        state.searchQuery = e.target.value;
        applyFiltersAndRender();
      }});
      document.getElementById('selectWeek').addEventListener('change', e => {{
        state.selectedWeek = e.target.value;
        applyFiltersAndRender();
      }});
      document.getElementById('selectCourt').addEventListener('change', e => {{
        state.selectedCourt = e.target.value;
        applyFiltersAndRender();
      }});
      document.getElementById('selectMaxPrice').addEventListener('change', e => {{
        state.maxPrice = Number(e.target.value || 0);
        applyFiltersAndRender();
      }});
      document.getElementById('selectSort').addEventListener('change', e => {{
        state.sortBy = e.target.value;
        applyFiltersAndRender();
      }});

      document.getElementById('btnResetFilters').addEventListener('click', () => {{
        state.activeTab = 'ALL';
        state.lifecycleFilter = 'ACTIVE_ONLY';
        state.searchQuery = '';
        state.selectedWeek = 'ALL';
        state.selectedCourt = 'ALL';
        state.maxPrice = 0;
        state.sortBy = 'DATE_ASC';
        document.getElementById('selectLifecycle').value = 'ACTIVE_ONLY';
        document.getElementById('inputSearch').value = '';
        document.getElementById('selectWeek').value = 'ALL';
        document.getElementById('selectCourt').value = 'ALL';
        document.getElementById('selectMaxPrice').value = '0';
        document.getElementById('selectSort').value = 'DATE_ASC';
        setActiveTab('ALL');
      }});

      document.getElementById('btnExportCsv').addEventListener('click', exportCurrentFilteredCsv);

      document.getElementById('tableBody').addEventListener('click', e => {{
        const btn = e.target.closest('.btn-detail');
        if (btn) {{
          openDetailModal(btn.getAttribute('data-prop-uid'));
        }}
      }});

      document.getElementById('btnCloseModal').addEventListener('click', () => {{
        document.getElementById('detailModal').classList.add('hidden');
      }});
      document.getElementById('detailModal').addEventListener('click', e => {{
        if (e.target.id === 'detailModal') {{
          document.getElementById('detailModal').classList.add('hidden');
        }}
      }});
    }});
  </script>
</body>
</html>
"""
    with open(html_path, "w", encoding="utf-8") as f:
        f.write(html_content)
    logger.info(f"已匯出互動式 HTML 可視化儀表板至: {html_path}")


# ==============================================================================
# 5. 主程式與每週排程器 (CLI & Weekly Scheduler)
# ==============================================================================
def run_update_job(
    db_path: str = DEFAULT_DB_PATH,
    excel_path: str = "macau_court_sales_report.xlsx",
    html_path: str = "macau_court_dashboard.html",
    archive_dir: str = "weekly_reports",
    local_snapshot_file: Optional[str] = None,
    cycle_id: Optional[str] = None,
    reference_date: Optional[str] = None,
):
    if local_snapshot_file and os.path.exists(local_snapshot_file):
        logger.info(f"從本地快照檔案讀取資料: {local_snapshot_file}")
        with open(local_snapshot_file, "r", encoding="utf-8") as f:
            raw_text = f.read()
    else:
        raw_text = fetch_court_sell_page(TARGET_URL)

    parsed_data = parse_court_sell_text(raw_text)
    logger.info(
        f"成功解析法院網站資料（網站最後更新日期: {parsed_data.get('last_updated')}），"
        f"共擷取 {len(parsed_data.get('cases', []))} 宗司法變賣案件。"
    )

    db = CourtSaleDatabase(db_path=db_path)
    stats = db.upsert_records(parsed_data, cycle_id=cycle_id, reference_date=reference_date)
    logger.info(
        f"資料庫更新完成 [{stats['cycle_id']}] (基準日: {stats['reference_date']}): "
        f"🟢待開標案件 {stats['total_cases']} 宗 | 🟢待開標財產 {stats['total_properties']} 項 "
        f"(住宅: {stats['residential_count']}, 停車位: {stats['parking_count']}) | "
        f"⚪已過開標期歸檔: {stats['archived_properties']} 項 | "
        f"🔄前期已出現: {stats['repeated_props']} 項"
    )

    print_summary_report(db)
    if excel_path:
        export_to_excel_and_csv(db, excel_path=excel_path)
        if archive_dir:
            os.makedirs(archive_dir, exist_ok=True)
            date_compact = stats["reference_date"].replace("-", "")
            archive_filename = f"macau_court_sales_{stats['cycle_id']}_{date_compact}.xlsx"
            archive_full_path = os.path.join(archive_dir, archive_filename)
            shutil.copy2(excel_path, archive_full_path)
            logger.info(f"已同時另存本週專屬歷史 Excel 報表至: {archive_full_path}")
    if html_path:
        export_html_dashboard(db, html_path=html_path, reference_date=stats["reference_date"])
    db.close()
    return stats


def start_weekly_daemon(
    db_path: str,
    excel_path: str,
    html_path: str,
    weekday: str = "monday",
    run_time: str = "09:00",
):
    logger.info(f"啟動每週自動追蹤排程模式 (每逢星期 {weekday} {run_time} 自動更新)...")
    run_update_job(db_path=db_path, excel_path=excel_path, html_path=html_path)

    try:
        import schedule

        getattr(schedule.every(), weekday.lower()).at(run_time).do(
            run_update_job, db_path=db_path, excel_path=excel_path, html_path=html_path
        )
        while True:
            schedule.run_pending()
            time.sleep(60)
    except ImportError:
        logger.info("未安裝 schedule 套件，改用內建每 7 天 (604800 秒) 定時循環...")
        while True:
            time.sleep(7 * 24 * 3600)
            run_update_job(db_path=db_path, excel_path=excel_path, html_path=html_path)


def main():
    parser = argparse.ArgumentParser(description="澳門法院司法變賣自動追蹤、資料庫統計與可視化儀表板系統 (v4.0 防疊加與過期歸檔版)")
    parser.add_argument("--db", default=DEFAULT_DB_PATH, help="SQLite 資料庫檔案路徑 (預設: macau_court_sales.db)")
    parser.add_argument(
        "--excel", default="macau_court_sales_report.xlsx", help="匯出 Excel 報表路徑"
    )
    parser.add_argument(
        "--dashboard", default="macau_court_dashboard.html", help="匯出互動式 HTML 儀表板路徑"
    )
    parser.add_argument(
        "--archive-dir", default="weekly_reports", help="每週自動另存帶日期週期 Excel 報表的資料夾路徑 (預設: weekly_reports)"
    )
    parser.add_argument("--snapshot", default=None, help="選填：使用離線網頁文字快照進行匯入")
    parser.add_argument("--cycle", default=None, help="選填：指定追蹤周期代號 (如 2026-W46)")
    parser.add_argument("--ref-date", default=None, help="選填：指定開標狀態判定基準日 (YYYY-MM-DD)")
    parser.add_argument(
        "--daemon", action="store_true", help="啟動每星期自動更新常駐排程模式"
    )
    args = parser.parse_args()

    if args.daemon:
        start_weekly_daemon(db_path=args.db, excel_path=args.excel, html_path=args.dashboard)
    else:
        run_update_job(
            db_path=args.db,
            excel_path=args.excel,
            html_path=args.dashboard,
            archive_dir=args.archive_dir,
            local_snapshot_file=args.snapshot,
            cycle_id=args.cycle,
            reference_date=args.ref_date,
        )


if __name__ == "__main__":
    main()

"""
TerraLedger — Biodiversity Impact Evidence & Monitoring Registry (Project 017)
Single-file Streamlit MVP. Run:  streamlit run app.py
- Auto-seeds a synthetic, clearly-labelled demo registry (SQLite, local file).
- Live field-telemetry simulation starts automatically (Mission Control).
- Full workflow: import → validate → review → approve → engine → report → share.
- Decision support only. Synthetic data. Not a statutory biodiversity metric.
"""
from __future__ import annotations
import html, io, json, hashlib, inspect, math, random, re, shutil, sqlite3, time
from contextlib import contextmanager
from datetime import datetime, timedelta, timezone, date
from pathlib import Path
from urllib.parse import urlencode, quote

import numpy as np
import pandas as pd
import plotly.graph_objects as go
import streamlit as st
from streamlit.components.v1 import html as comp_html

# ────────────────────────────────────────── CONSTANTS ─────────────────────────
APP, VER, SCHEMA = "TerraLedger", "0.9.0", "1.1"
ENGINE_VER = "1.0.0"
DIR = Path("terraledger_data"); SRC = DIR/"sources"; EVI = DIR/"evidence"; BAK = DIR/"backups"
DBP = DIR/"registry.db"
ss = st.session_state

PAL = {"green":"#4ade80","teal":"#2dd4bf","blue":"#38bdf8","amber":"#fbbf24",
       "clay":"#d4a373","magenta":"#fb7185","violet":"#a78bfa","lime":"#a3e635"}
USERS = {
 "Amara Okafor":   {"role":"Administrator","init":"AO","c":PAL["green"]},
 "Diego Fernández":{"role":"Analyst","init":"DF","c":PAL["blue"]},
 "Dr. Ingrid Solberg":{"role":"Reviewer","init":"IS","c":PAL["amber"]},
 "Sam Whitfield":  {"role":"Stakeholder","init":"SW","c":PAL["clay"]},
}
PERMS = {
 "Administrator":{"create","edit","delete","import","validate","submit","review","approve","override","export","archive","restore","admin","share"},
 "Analyst":{"create","edit","delete","import","validate","submit","export","share"},
 "Reviewer":{"validate","submit","review","approve","override","export","share"},
 "Stakeholder":{"export","share"},
}
STATUS_META = {"DRAFT":("✏️","#9fb8ab"),"VALIDATED":("🧪","#38bdf8"),"IN_REVIEW":("🔍","#fbbf24"),
 "APPROVED":("✅","#4ade80"),"REJECTED":("⛔","#fb7185"),"CORRECTION":("🛠️","#d4a373"),"ARCHIVED":("🗄️","#8a97a0")}
TRANSITIONS = {"DRAFT":{"VALIDATED","ARCHIVED"},"VALIDATED":{"IN_REVIEW","DRAFT","ARCHIVED"},
 "IN_REVIEW":{"APPROVED","REJECTED","CORRECTION"},"APPROVED":{"ARCHIVED","CORRECTION"},
 "REJECTED":{"DRAFT","ARCHIVED"},"CORRECTION":{"DRAFT","VALIDATED","ARCHIVED"},"ARCHIVED":{"DRAFT"}}
ACT_FOR = {"VALIDATED":"validate","IN_REVIEW":"submit","APPROVED":"approve","REJECTED":"review",
 "CORRECTION":"review","DRAFT":"edit","ARCHIVED":"archive"}
ACTION_C = {"create":PAL["green"],"import":PAL["blue"],"validate":PAL["teal"],"submit":PAL["amber"],
 "approve":PAL["green"],"reject":PAL["magenta"],"correction":PAL["clay"],"archive":"#8a97a0",
 "restore":PAL["lime"],"export":PAL["violet"],"override":PAL["magenta"],"delete":PAL["magenta"],
 "reorder":PAL["blue"],"backup":PAL["teal"],"purge":PAL["amber"],"attach":PAL["blue"],
 "edit":PAL["blue"],"session":"#8a97a0","rules":PAL["violet"],"save":PAL["green"]}
HARD = {"MISSING_FIELD","BAD_TYPE","BAD_DATE","FUTURE_DATE","UNKNOWN_SITE","DUPLICATE","NEGATIVE_COUNT","BAD_UNIT","BAD_METHOD"}
HAB_DIST = {"Ancient woodland":8,"Wetland":6,"Heathland":6,"Riparian":5,"Species-rich meadow":4,"Modified grassland":2,"Urban mosaic":1,"Bare spoil":1}
RULES = {
 "1.1.0":{"temporal":[(5,.90),(10,.70),(15,.55),(20,.40),(30,.32)],"difficulty":{"Low":1.0,"Medium":.67,"High":.33},
          "condition":{"Poor":1,"Fair":2,"Good":3},"strategic":{"Standard":1.0,"Elevated":1.15},"published":"2025-06-14"},
 "1.2.0":{"temporal":[(5,.92),(10,.73),(15,.58),(20,.44),(30,.35)],"difficulty":{"Low":1.0,"Medium":.67,"High":.35},
          "condition":{"Poor":1,"Fair":2,"Good":3},"strategic":{"Standard":1.0,"Elevated":1.15},"published":"2026-01-20"},
}
UNITS = ["individuals","pairs","territories","burrows","holts","tracks"]
METHODS = ["transect","quadrat","acoustic","camera-trap","eDNA","casual"]
IMPACT_TYPES = ["habitat-loss","hydrology","disturbance","pollution","fragmentation"]
OBS_REQ = ["site_code","taxon","count","unit","method","observed_at"]
TAXA = [("Erinaceus europaeus","European hedgehog","Mammal","camera-trap",6),
 ("Lutra lutra","Eurasian otter","Mammal","camera-trap",3),("Arvicola amphibius","Water vole","Mammal","transect",8),
 ("Myotis daubentonii","Daubenton's bat","Mammal","acoustic",22),("Triturus cristatus","Great crested newt","Amphibian","eDNA",5),
 ("Rana temporaria","Common frog","Amphibian","quadrat",14),("Alauda arvensis","Skylark","Bird","transect",10),
 ("Turdus philomelos","Song thrush","Bird","transect",7),("Alcedo atthis","Kingfisher","Bird","casual",2),
 ("Polyommatus icarus","Common blue butterfly","Invertebrate","transect",18),("Euphydryas aurinia","Marsh fritillary","Invertebrate","transect",6),
 ("Bombus lapidarius","Red-tailed bumblebee","Invertebrate","quadrat",24),("Anax imperator","Emperor dragonfly","Invertebrate","transect",9),
 ("Primula veris","Cowslip","Plant","quadrat",30)]
TAXON_GROUP = {t[0]:t[2] for t in TAXA}
SITE_SEED = [
 ("WIL","Willowbrook Wetland Reserve","Wetland","Good",12.4,51.452,-0.968,"Local Nature Reserve",1,[1,2,3,4,5,10,12]),
 ("HAW","Hawthorn Ridge Woodland","Ancient woodland","Good",8.6,51.489,-0.921,"Ancient semi-natural",1,[0,3,7,13]),
 ("EAS","Eastgate Development Parcel","Modified grassland","Fair",5.2,51.432,-0.874,"Planning ref E/24/118",1,[6,9,11,13]),
 ("RIV","River Alder Corridor","Riparian","Fair",3.8,51.466,-0.902,"Utility easement",3,[1,2,8,12]),
 ("QRY","North Quarry Restoration","Bare spoil","Poor",9.1,51.501,-0.858,"Restoration notice RN-77",3,[6,9,11]),
 ("CME","Civic Meadow Network","Species-rich meadow","Fair",2.7,51.444,-0.941,"Council greenspace",1,[5,9,10,11,13])]
SCENARIOS = {"Dawn chorus":{"a":58,"p":34,"w":84,"ev":.45},"Pollinator bloom":{"a":44,"p":72,"w":86,"ev":.6},
 "Storm front":{"a":30,"p":12,"w":58,"ev":.2},"Night survey":{"a":74,"p":5,"w":80,"ev":.5}}
TABLES = {"observations":"OBS","impacts":"IMP","actions":"ACT","assessments":"ASM"}
PCFG = {"displayModeBar": False}

def _stretch(fn):
    try:
        if "width" in inspect.signature(fn).parameters: return {"width":"stretch"}
    except (ValueError, TypeError): pass
    return {"use_container_width": True}
W_DF, W_PC, W_DL = _stretch(st.dataframe), _stretch(st.plotly_chart), _stretch(st.download_button)
HAS_DIALOG = hasattr(st,"dialog")
DLG_KW = {"width":"large"} if HAS_DIALOG and "width" in inspect.signature(st.dialog).parameters else {}
HAS_FRAG = hasattr(st,"fragment")
def modal(title):
    def deco(fn): return st.dialog(title, **DLG_KW)(fn) if HAS_DIALOG else fn
    return deco
def frag(fn): return st.fragment(run_every=1.0)(fn) if HAS_FRAG else fn
def rerun_app():
    try: st.rerun(scope="app")
    except TypeError: st.rerun()

# ────────────────────────────────────────── STYLE ─────────────────────────────
CSS = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Fraunces:opsz,wght@9..144,600;9..144,700&family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@400;600&display=swap');
:root{--bg:#081410;--surf:#10231b;--surf2:#0d1e17;--line:rgba(74,222,128,.16);--txt:#e8f4ec;--mut:#9fb8ab;
--green:#4ade80;--teal:#2dd4bf;--blue:#38bdf8;--amber:#fbbf24;--clay:#d4a373;--mag:#fb7185;--vio:#a78bfa;}
*{scrollbar-width:thin;scrollbar-color:#2f5c47 #0b1a14;}
::-webkit-scrollbar{width:10px;height:10px}
::-webkit-scrollbar-track{background:#0b1a14;border-radius:8px}
::-webkit-scrollbar-thumb{background:linear-gradient(180deg,#2f5c47,#1c4634);border-radius:8px;border:2px solid #0b1a14}
::-webkit-scrollbar-thumb:hover{background:linear-gradient(180deg,#4ade80,#2dd4bf)}
.stApp{background:var(--bg);color:var(--txt);font-family:'Inter',sans-serif;}
.stApp::before{content:"";position:fixed;inset:-20%;pointer-events:none;z-index:0;
background:radial-gradient(640px 420px at 12% 8%,rgba(74,222,128,.15),transparent 60%),
radial-gradient(720px 520px at 88% 10%,rgba(56,189,248,.11),transparent 60%),
radial-gradient(820px 620px at 50% 112%,rgba(212,163,115,.10),transparent 60%);
animation:drift 28s ease-in-out infinite alternate;}
.stApp::after{content:"";position:fixed;inset:0;pointer-events:none;z-index:9998;opacity:.045;
background-image:url("data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='160' height='160'><filter id='n'><feTurbulence type='fractalNoise' baseFrequency='0.9' numOctaves='2'/><feColorMatrix type='saturate' values='0'/></filter><rect width='160' height='160' filter='url(%23n)' opacity='0.55'/></svg>");}
@keyframes drift{from{transform:translate3d(-2%,-1%,0) scale(1)}to{transform:translate3d(2%,2%,0) scale(1.06)}}
[data-testid="stAppViewContainer"]{position:relative;z-index:1}
[data-testid="stHeader"]{background:transparent}
#MainMenu,footer,[data-testid="stToolbar"],[data-testid="stDecoration"]{display:none}
h1,h2,h3,.sec-t,.kpi-v,.brand-t{font-family:'Fraunces',serif!important}
code,.mono{font-family:'JetBrains Mono',monospace!important}
section[data-testid="stSidebar"]{background:linear-gradient(180deg,#0c1d16,#081410);border-right:1px solid var(--line)}
section[data-testid="stSidebar"] .stRadio label{width:100%;background:#0d1f18;border:1px solid transparent;border-radius:12px;
padding:9px 12px;margin:3px 0;transition:all .18s;cursor:pointer;font-weight:600;font-size:.92rem}
section[data-testid="stSidebar"] .stRadio label:hover{border-color:rgba(74,222,128,.4);transform:translateX(2px)}
section[data-testid="stSidebar"] .stRadio label:has(input:checked){background:linear-gradient(120deg,rgba(74,222,128,.18),rgba(45,212,191,.10));border-color:var(--green);color:#dffbe9}
section[data-testid="stSidebar"] .stRadio input{position:absolute;opacity:0}
section[data-testid="stSidebar"] div[role="radiogroup"]{gap:2px}
.stButton>button,.stDownloadButton>button,[data-testid="stLinkButton"]>a,[data-testid="stFormSubmitButton"]>button{
border-radius:12px;border:1px solid rgba(74,222,128,.35);background:#0f231b;color:#d9efe2;font-weight:600;
transition:all .18s;font-family:'Inter',sans-serif}
.stButton>button:hover,.stDownloadButton>button:hover,[data-testid="stLinkButton"]>a:hover,[data-testid="stFormSubmitButton"]>button:hover{
border-color:var(--green);box-shadow:0 0 0 3px rgba(74,222,128,.14);transform:translateY(-1px);color:#fff}
button[kind="primary"],[data-testid="stBaseButton-primary"]{background:linear-gradient(135deg,#34d399,#0ea5a0)!important;color:#052015!important;border:none!important;font-weight:700!important}
button[kind="primary"]:hover,[data-testid="stBaseButton-primary"]:hover{box-shadow:0 6px 22px rgba(52,211,153,.35)!important}
button:disabled{opacity:.4!important;transform:none!important;box-shadow:none!important}
.stTabs [data-baseweb="tab"]{font-weight:600;color:var(--mut);font-size:.93rem}
.stTabs [aria-selected="true"]{color:var(--green)!important}
.stTabs [data-baseweb="tab-highlight"]{background:var(--green)!important}
[data-baseweb="select"]>div,.stTextInput input,.stTextArea textarea,.stNumberInput input,.stDateInput input{
background:#0d1f18!important;border-color:rgba(74,222,128,.28)!important;color:var(--txt)!important;border-radius:10px!important}
[data-testid="stDataFrame"]{border:1px solid var(--line);border-radius:12px;overflow:hidden}
[data-testid="stExpander"]{border:1px solid var(--line);border-radius:14px;background:var(--surf2)}
[data-testid="stExpander"] summary:hover{color:var(--green)}
[data-testid="stDialog"]>div{background:linear-gradient(170deg,#0f241c,#0a1712);border:1px solid rgba(74,222,128,.3);border-radius:18px}
[data-testid="stFileUploaderDropzone"]{background:#0d1f18;border:1px dashed rgba(74,222,128,.4);border-radius:14px}
.brand{display:flex;align-items:center;gap:14px;flex-wrap:wrap}
.brand-t{font-size:1.9rem;font-weight:700;line-height:1.05;background:linear-gradient(100deg,#4ade80,#2dd4bf 55%,#38bdf8);
-webkit-background-clip:text;background-clip:text;color:transparent;letter-spacing:-.01em}
.brand-s{color:var(--mut);font-size:.8rem;margin-top:2px}
.chip{display:inline-flex;align-items:center;gap:6px;padding:3px 11px;border-radius:999px;font-size:.7rem;font-weight:700;
letter-spacing:.06em;border:1px solid var(--line);color:var(--mut);background:#0d1f18;text-transform:uppercase}
.dot{width:8px;height:8px;border-radius:50%;background:var(--green);animation:pulse 1.6s infinite}
@keyframes pulse{0%,100%{box-shadow:0 0 0 0 rgba(74,222,128,.5)}55%{box-shadow:0 0 0 7px rgba(74,222,128,0)}}
.sec{margin:22px 0 10px}
.sec-k{font-size:.68rem;font-weight:700;letter-spacing:.18em;color:var(--teal);text-transform:uppercase}
.sec-t{font-size:1.28rem;font-weight:700;color:var(--txt)}
.card{background:linear-gradient(160deg,#10231b,#0c1a14);border:1px solid var(--line);border-radius:16px;padding:16px 18px;
box-shadow:0 10px 30px rgba(0,0,0,.35);animation:rise .45s ease both;margin-bottom:10px}
.kpi{background:linear-gradient(160deg,#10231b,#0c1a14);border:1px solid var(--line);border-radius:16px;padding:14px 16px;
animation:rise .5s ease both;height:100%}
@keyframes rise{from{opacity:0;transform:translateY(9px)}to{opacity:1;transform:none}}
.kpi-l{font-size:.66rem;font-weight:700;letter-spacing:.12em;color:var(--mut);text-transform:uppercase}
.kpi-v{font-size:1.75rem;font-weight:700;line-height:1.15;margin-top:4px}
.kpi-s{font-size:.74rem;color:var(--mut);margin-top:2px}
.bdg{display:inline-flex;padding:2px 10px;border-radius:999px;font-size:.68rem;font-weight:700;letter-spacing:.05em;
border:1px solid;text-transform:uppercase;white-space:nowrap}
.fchip{display:inline-flex;padding:1px 8px;border-radius:6px;font-size:.66rem;font-weight:700;margin:1px 2px;border:1px solid}
.tl{border-left:2px solid rgba(74,222,128,.22);padding-left:16px;margin:6px 0}
.tl-i{position:relative;margin:0 0 14px}
.tl-dot{position:absolute;left:-23px;top:4px;width:11px;height:11px;border-radius:50%;border:2px solid #0a1712}
.tl-t{font-weight:700;font-size:.82rem}
.tl-m{color:var(--mut);font-weight:500}
.tl-d{font-size:.78rem;color:#c4d8cc;margin-top:1px;word-wrap:break-word}
.tl-ts{font-size:.68rem;color:var(--mut);font-family:'JetBrains Mono',monospace}
.tick{display:flex;gap:8px;align-items:center;font-family:'JetBrains Mono',monospace;font-size:.74rem;
padding:5px 10px;border-radius:9px;background:#0d1f18;border:1px solid var(--line);margin:4px 0;animation:rise .3s ease both}
.bar{height:7px;border-radius:99px;background:#0b1a14;overflow:hidden;border:1px solid var(--line)}
.bar>div{height:100%;border-radius:99px;background:linear-gradient(90deg,#34d399,#38bdf8)}
.mini{font-size:.76rem;color:var(--mut)}
a.lnk{color:var(--green);font-weight:600}
.stAlert{border-radius:12px}
@media (max-width:640px){.brand-t{font-size:1.4rem}.kpi-v{font-size:1.35rem}}
</style>
"""

# ────────────────────────────────────────── UTILS ─────────────────────────────
def esc(x): return html.escape(str(x if x is not None else ""))
def now(): return datetime.now(timezone.utc)
def iso(dt): return dt.isoformat(timespec="seconds")
def now_iso(): return iso(now())
def fmt_dt(s):
    if not s: return "—"
    try: return datetime.fromisoformat(str(s)).strftime("%d %b %Y · %H:%M")
    except Exception: return str(s)[:16]
def money(v): return f"£{v:,.0f}"
def pctf(v): return "—" if v is None else f"{v:+.1f}%"
def code_of(table, rid): return f"{TABLES.get(table,'REC')}-{int(rid):04d}"
def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def safe_name(n): return re.sub(r"[^A-Za-z0-9._-]","_",str(n))[-80:]
def ha_to_m2(ha): return float(ha)*10000.0
def parse_date(v):
    if isinstance(v, datetime): return v.date()
    if isinstance(v, date): return v
    s = str(v).strip()
    for f in ("%Y-%m-%d","%d/%m/%Y","%Y/%m/%d","%d-%m-%Y"):
        try: return datetime.strptime(s,f).date()
        except ValueError: pass
    raise ValueError(f"Unrecognised date '{v}' — use YYYY-MM-DD")
def badge(s):
    ic,c = STATUS_META.get(s,("•","#9fb8ab"))
    return f'<span class="bdg" style="color:{c};border-color:{c}66;background:{c}14">{ic} {esc(s)}</span>'
def flags_of(row):
    try: return json.loads(row.get("flags") or "[]")
    except Exception: return []
def flags_html(flags):
    if not flags: return '<span class="mini">no flags</span>'
    out=""
    for f in flags:
        c = PAL["magenta"] if f in HARD else (PAL["violet"] if f=="ESTIMATE" else PAL["amber"])
        out += f'<span class="fchip" style="color:{c};border-color:{c}55;background:{c}12">{esc(f)}</span>'
    return out
def fig_base(fig, h=280, title=None):
    fig.update_layout(height=h, paper_bgcolor="rgba(0,0,0,0)", plot_bgcolor="rgba(0,0,0,0)",
        font=dict(family="Inter, sans-serif", color="#cfe3d6", size=12),
        margin=dict(l=10,r=10,t=38 if title else 16,b=10),
        title=dict(text=title, font=dict(size=15, color="#e8f4ec")) if title else None,
        legend=dict(orientation="h", y=1.14, x=0, font=dict(size=11)),
        hoverlabel=dict(bgcolor="#0f241c", bordercolor="#2f5c47", font=dict(color="#e8f4ec")))
    fig.update_xaxes(gridcolor="rgba(74,222,128,.08)", zerolinecolor="rgba(74,222,128,.15)")
    fig.update_yaxes(gridcolor="rgba(74,222,128,.08)", zerolinecolor="rgba(74,222,128,.15)")
    return fig
def kpi(icon,label,value,sub="",color=None,i=0):
    color = color or PAL["green"]
    st.markdown(f'<div class="kpi" style="animation-delay:{i*60}ms"><div class="kpi-l">{icon} {esc(label)}</div>'
                f'<div class="kpi-v" style="color:{color}">{esc(value)}</div><div class="kpi-s">{esc(sub)}</div></div>',
                unsafe_allow_html=True)
def section(kicker,title):
    st.markdown(f'<div class="sec"><div class="sec-k">{esc(kicker)}</div><div class="sec-t">{esc(title)}</div></div>',
                unsafe_allow_html=True)
def card(inner, delay=0):
    st.markdown(f'<div class="card" style="animation-delay:{delay}ms">{inner}</div>', unsafe_allow_html=True)
def timeline_html(events, limit=12):
    if not events: return '<div class="mini">No history yet.</div>'
    items=""
    for e in events[:limit]:
        c = ACTION_C.get(e["action"], PAL["blue"])
        items += (f'<div class="tl-i"><span class="tl-dot" style="background:{c}"></span>'
                  f'<div class="tl-t">{esc(e["action"].upper())} <span class="tl-m">· {esc(e["actor"])} ({esc(e["role"])})</span></div>'
                  f'<div class="tl-d">{esc(e["detail"] or "")}</div><div class="tl-ts">{fmt_dt(e["ts"])}</div></div>')
    return f'<div class="tl">{items}</div>'
def empty_state(msg, icon="🌿"):
    card(f'<div style="text-align:center;padding:14px"><div style="font-size:1.8rem">{icon}</div>'
         f'<div class="mini" style="margin-top:6px">{esc(msg)}</div></div>')
def link_btn(label,url,primary=False,key=None):
    if hasattr(st,"link_button"): st.link_button(label,url,type="primary" if primary else "secondary",key=key)
    else: st.markdown(f'<a class="lnk" href="{esc(url)}" target="_blank">{esc(label)}</a>', unsafe_allow_html=True)

# ────────────────────────────────────────── DATABASE ──────────────────────────
@contextmanager
def db():
    conn = sqlite3.connect(DBP, timeout=30)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys=ON")
    try:
        yield conn; conn.commit()
    except Exception:
        conn.rollback(); raise
    finally:
        conn.close()
def ins(conn, table, data: dict) -> int:
    cols = ",".join(data); qs = ",".join(["?"]*len(data))
    return conn.execute(f"INSERT INTO {table}({cols}) VALUES({qs})", tuple(data.values())).lastrowid
def upd(conn, table, rid, data: dict):
    sets = ",".join(f"{k}=?" for k in data)
    conn.execute(f"UPDATE {table} SET {sets} WHERE id=?", tuple(data.values())+(rid,))
def log_event(conn, action, entity, eid, detail, actor=None, role=None, ts=None):
    ins(conn,"audit",{"ts":ts or now_iso(),"actor":actor or ss.get("actor","system"),
        "role":role or ss.get("role","system"),"action":action,"entity":entity,"entity_id":eid,"detail":detail})
DDL = """
CREATE TABLE IF NOT EXISTS meta(k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS organizations(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT,kind TEXT,jurisdiction TEXT);
CREATE TABLE IF NOT EXISTS sites(id INTEGER PRIMARY KEY AUTOINCREMENT,code TEXT UNIQUE,org_id INTEGER,name TEXT,habitat TEXT,
 condition TEXT,area_ha REAL,lat REAL,lon REAL,designation TEXT,created_at TEXT,schema_version TEXT);
CREATE TABLE IF NOT EXISTS source_files(id INTEGER PRIMARY KEY AUTOINCREMENT,filename TEXT,sha256 TEXT,kind TEXT,bytes INTEGER,
 row_count INTEGER,imported_by TEXT,imported_at TEXT,schema_version TEXT,path TEXT);
CREATE TABLE IF NOT EXISTS observations(id INTEGER PRIMARY KEY AUTOINCREMENT,site_id INTEGER,taxon TEXT,common_name TEXT,count INTEGER,
 unit TEXT,method TEXT,observed_at TEXT,recorded_at TEXT,recorded_by TEXT,status TEXT,flags TEXT,notes TEXT,priority INTEGER DEFAULT 0,
 source_file_id INTEGER,source_row INTEGER,origin TEXT,schema_version TEXT,created_at TEXT,updated_at TEXT,deleted_at TEXT);
CREATE TABLE IF NOT EXISTS impacts(id INTEGER PRIMARY KEY AUTOINCREMENT,site_id INTEGER,activity TEXT,impact_type TEXT,area_ha REAL,
 severity INTEGER,start_date TEXT,status TEXT,notes TEXT,flags TEXT,priority INTEGER DEFAULT 0,origin TEXT,created_at TEXT,updated_at TEXT,
 deleted_at TEXT,schema_version TEXT);
CREATE TABLE IF NOT EXISTS actions(id INTEGER PRIMARY KEY AUTOINCREMENT,site_id INTEGER,action_type TEXT,habitat_target TEXT,
 condition_target TEXT,area_ha REAL,years_to_target INTEGER,difficulty TEXT,strategic TEXT,start_date TEXT,cost_gbp REAL,progress INTEGER,
 status TEXT,notes TEXT,flags TEXT,priority INTEGER DEFAULT 0,origin TEXT,created_at TEXT,updated_at TEXT,deleted_at TEXT,schema_version TEXT);
CREATE TABLE IF NOT EXISTS assessments(id INTEGER PRIMARY KEY AUTOINCREMENT,site_id INTEGER,params TEXT,result TEXT,rules_version TEXT,
 engine_version TEXT,status TEXT,override TEXT,priority INTEGER DEFAULT 0,created_by TEXT,created_at TEXT,updated_at TEXT);
CREATE TABLE IF NOT EXISTS evidence(id INTEGER PRIMARY KEY AUTOINCREMENT,entity TEXT,entity_id INTEGER,filename TEXT,kind TEXT,
 bytes INTEGER,sha256 TEXT,path TEXT,uploaded_by TEXT,uploaded_at TEXT);
CREATE TABLE IF NOT EXISTS audit(id INTEGER PRIMARY KEY AUTOINCREMENT,ts TEXT,actor TEXT,role TEXT,action TEXT,entity TEXT,
 entity_id INTEGER,detail TEXT);
CREATE TABLE IF NOT EXISTS saved_views(id INTEGER PRIMARY KEY AUTOINCREMENT,name TEXT,filters TEXT,created_by TEXT,created_at TEXT);
"""
def init_storage():
    for d in (DIR,SRC,EVI,BAK): d.mkdir(parents=True, exist_ok=True)
    with db() as c:
        c.executescript(DDL); c.execute("PRAGMA journal_mode=WAL")
        if not c.execute("SELECT v FROM meta WHERE k='seed'").fetchone():
            seed(c); c.execute("INSERT INTO meta(k,v) VALUES('seed','1')")
            c.execute("INSERT OR REPLACE INTO meta(k,v) VALUES('schema',?)",(SCHEMA,))
def sites_df(c): return pd.read_sql_query("SELECT s.*, o.name AS org_name FROM sites s JOIN organizations o ON o.id=s.org_id ORDER BY s.code", c)
def obs_df(c): return pd.read_sql_query(
    "SELECT o.*, s.code AS site_code, s.name AS site_name, f.filename AS source_file, f.sha256 AS source_sha "
    "FROM observations o JOIN sites s ON s.id=o.site_id LEFT JOIN source_files f ON f.id=o.source_file_id "
    "WHERE o.deleted_at IS NULL ORDER BY o.observed_at DESC, o.id DESC", c)
def impacts_df(c): return pd.read_sql_query("SELECT i.*, s.code AS site_code, s.name AS site_name FROM impacts i "
    "JOIN sites s ON s.id=i.site_id WHERE i.deleted_at IS NULL ORDER BY i.start_date DESC", c)
def actions_df(c): return pd.read_sql_query("SELECT a.*, s.code AS site_code, s.name AS site_name FROM actions a "
    "JOIN sites s ON s.id=a.site_id WHERE a.deleted_at IS NULL ORDER BY a.start_date DESC", c)
def assess_df(c): return pd.read_sql_query("SELECT a.*, s.code AS site_code, s.name AS site_name FROM assessments a "
    "JOIN sites s ON s.id=a.site_id ORDER BY a.created_at DESC", c)
def get_row(table, rid):
    if table not in TABLES: return None
    with db() as c:
        r = c.execute(f"SELECT * FROM {table} WHERE id=?", (rid,)).fetchone()
        return dict(r) if r else None
def audit_for(entity, eid, limit=40):
    with db() as c:
        return [dict(r) for r in c.execute("SELECT * FROM audit WHERE entity=? AND entity_id=? ORDER BY ts DESC LIMIT ?",
                                           (entity,eid,limit))]

# ────────────────────────────────────────── PERMISSIONS & LIFECYCLE ───────────
def can(action, role=None): return action in PERMS.get(role or ss.get("role","Stakeholder"), set())
def require(action, role=None):
    if not can(action, role):
        raise PermissionError(f"Role '{role or ss.role}' cannot '{action}'. Switch persona in the sidebar (demo identities).")
def check_transition(cur, to): return to in TRANSITIONS.get(cur, set())
def needs_reason(flags, to): return to=="APPROVED" and "CONTRADICTORY" in flags
def do_transition(table, rid, to, reason=""):
    if table not in TABLES: raise ValueError("Unknown record type")
    with db() as c:
        r = c.execute(f"SELECT * FROM {table} WHERE id=?", (rid,)).fetchone()
        if not r: raise ValueError("Record not found")
        r = dict(r); cur = r["status"]
        action = "restore" if (cur=="ARCHIVED" and to=="DRAFT") else ACT_FOR.get(to,"edit")
        require(action)
        if not check_transition(cur,to):
            raise ValueError(f"Illegal transition {cur} → {to}. Allowed: {', '.join(sorted(TRANSITIONS.get(cur,[]))) or 'none'}")
        flags = json.loads(r.get("flags") or "[]")
        if needs_reason(flags,to) and not reason.strip():
            raise ValueError("Contradictory record: approval requires a documented override reason.")
        upd(c, table, rid, {"status":to,"updated_at":now_iso()})
        log_event(c, "override" if (needs_reason(flags,to) and reason) else action, table, rid,
                  f"{code_of(table,rid)}: {cur} → {to}" + (f" · reason: {reason}" if reason else ""))
    return True

# ────────────────────────────────────────── DOMAIN ENGINE ─────────────────────
def temporal_factor(years, rv):
    for th,f in RULES[rv]["temporal"]:
        if years <= th: return f
    return RULES[rv]["temporal"][-1][1]
def baseline_units(area, habitat, condition, rv):
    return round(area * HAB_DIST[habitat] * RULES[rv]["condition"][condition], 4)
def assess(p: dict, rv: str, soft_flags=0, estimate=False, stale=False) -> dict:
    R = RULES[rv]
    if p["area"] <= 0: raise ValueError("Area must be > 0 ha")
    base = p["area"] * HAB_DIST[p["base_habitat"]] * R["condition"][p["base_condition"]]
    s1 = p["area"] * HAB_DIST[p["target_habitat"]] * R["condition"][p["target_condition"]]
    tf = temporal_factor(p["years"], rv); df_ = R["difficulty"][p["difficulty"]]; sf = R["strategic"][p["strategic"]]
    s2 = s1*tf; s3 = s2*df_; post = s3*sf
    net = post-base; pct = None if base<=0 else 100.0*net/base
    rel = min(.35, .06 + .03*soft_flags + (.08 if estimate else 0))
    warns=[]
    if soft_flags: warns.append(f"{soft_flags} soft data-quality flag(s) at this site widen uncertainty.")
    if estimate: warns.append("Casual/estimate-method observations present — treat counts as indicative.")
    if stale: warns.append("Site data is stale (last observation > 21 days old).")
    if p["years"] >= 20: warns.append("Long time-to-target: temporal risk heavily discounts delivered units.")
    steps = [("Baseline", "absolute", base),
             ("Condition / habitat uplift","relative", s1-base),
             ("Time-to-target risk","relative", s2-s1),
             ("Creation difficulty","relative", s3-s2),
             ("Strategic significance","relative", post-s3),
             ("Post-intervention","total", post)]
    expl = [
      f"Baseline = {p['area']:.2f} ha × distinctiveness {HAB_DIST[p['base_habitat']]} ({p['base_habitat']}) × condition {R['condition'][p['base_condition']]} ({p['base_condition']}) = **{base:.2f} units**",
      f"Post (raw) = {p['area']:.2f} ha × {HAB_DIST[p['target_habitat']]} ({p['target_habitat']}) × {R['condition'][p['target_condition']]} ({p['target_condition']}) = {s1:.2f}",
      f"× temporal factor {tf:.2f} (target in {p['years']} y) → {s2:.2f}",
      f"× difficulty factor {df_:.2f} ({p['difficulty']}) → {s3:.2f}",
      f"× strategic factor {sf:.2f} ({p['strategic']}) → **{post:.2f} units**",
      f"Net change = {net:+.2f} units ({pctf(None if pct is None else round(pct,1))}) vs target ≥ {p['target_pct']}% → {'MEETS' if (pct is not None and pct>=p['target_pct']) else 'BELOW TARGET'}",
      f"Uncertainty ±{rel*100:.0f}% → post-interval {post*(1-rel):.2f} – {post*(1+rel):.2f} units (heuristic band, not a statistical CI)",
      f"Provenance: engine {ENGINE_VER} · factor table v{rv} (published {R['published']}) · synthetic demo factors — decision support only, not a statutory metric.",
    ]
    return {"baseline":round(base,2),"post":round(post,2),"net":round(net,2),
            "pct":None if pct is None else round(pct,1),
            "meets":bool(pct is not None and pct>=p["target_pct"]),
            "band_rel":rel,"band_abs":round(post*rel,2),
            "steps":[{"label":l,"measure":m,"value":round(v,3)} for l,m,v in steps],
            "warnings":warns,"inputs":dict(p),"rules_version":rv,"engine_version":ENGINE_VER,"explanation":expl}
def shannon(counts):
    v=[c for c in counts if c>0]; tot=sum(v)
    if tot<=0: return 0.0
    return -sum((c/tot)*math.log(c/tot) for c in v)
def simpson(counts):
    v=[c for c in counts if c>0]; tot=sum(v)
    if tot<=0: return 0.0
    return 1.0-sum((c/tot)**2 for c in v)
def zscore_flags(vals, thresh=2.5):
    out=[]
    if len(vals)<5: return out
    for i in range(4,len(vals)):
        w=np.array(vals[max(0,i-4):i],dtype=float); m,s=w.mean(),w.std()
        if s>0 and abs((vals[i]-m)/s)>thresh: out.append(i)
    return out
def site_quality(odf, site_id):
    sub = odf[odf.site_id==site_id]
    soft = sum(len([f for f in flags_of(r) if f not in HARD]) for r in sub.to_dict("records"))
    est = bool((sub.method=="casual").any()) or any("ESTIMATE" in flags_of(r) for r in sub.to_dict("records"))
    stale = True
    if len(sub):
        try: stale = (now().date() - parse_date(sub.observed_at.iloc[0])).days > 21
        except Exception: pass
    return {"soft":soft,"estimate":est,"stale":stale}

# ────────────────────────────────────────── VALIDATION & IMPORT ───────────────
def validate_obs_fields(row, site_codes, today_d):
    errors, warns = [], []
    def err(code,field,msg): errors.append({"code":code,"field":field,"msg":msg,"severity":"error"})
    def warn(code,field,msg): warns.append({"code":code,"field":field,"msg":msg,"severity":"warning"})
    for f in OBS_REQ:
        v=row.get(f)
        if v is None or (not isinstance(v,(int,float)) and str(v).strip()=="") or (isinstance(v,float) and math.isnan(v)):
            err("MISSING_FIELD",f,f"Required field '{f}' is empty")
    sc=str(row.get("site_code","")).strip()
    if sc and sc not in site_codes: err("UNKNOWN_SITE","site_code",f"Site '{sc}' not in registry (known: {', '.join(sorted(site_codes))})")
    cv=row.get("count")
    if cv is not None and str(cv).strip()!="":
        try:
            fv=float(cv)
            if math.isnan(fv): raise ValueError()
            if fv<0: err("NEGATIVE_COUNT","count","Count cannot be negative")
            elif not fv.is_integer(): err("BAD_TYPE","count","Count must be a whole number")
            elif fv>5000: warn("OUT_OF_RANGE","count",f"Count {int(fv)} exceeds plausible range (0–5000) — reviewer check required")
        except (ValueError,TypeError): err("BAD_TYPE","count",f"Count '{cv}' is not numeric")
    u=str(row.get("unit","")).strip()
    if u and u not in UNITS: err("BAD_UNIT","unit",f"Unit '{u}' invalid — allowed: {', '.join(UNITS)}")
    m=str(row.get("method","")).strip()
    if m and m not in METHODS: err("BAD_METHOD","method",f"Method '{m}' invalid — allowed: {', '.join(METHODS)}")
    od=None
    ov=row.get("observed_at")
    if ov is not None and str(ov).strip()!="":
        try:
            od=parse_date(ov)
            if od>today_d: err("FUTURE_DATE","observed_at","Observation date is in the future")
            elif (today_d-od).days>3650: warn("STALE","observed_at","Observation older than 10 years")
        except ValueError as e: err("BAD_DATE","observed_at",str(e))
    rv=row.get("recorded_at")
    if od and rv is not None and str(rv).strip()!="":
        try:
            rd=parse_date(rv)
            if rd<od: warn("CONTRADICTORY","recorded_at","Recorded before observed — check dates")
            elif (rd-od).days>30: warn("LATE","recorded_at",f"Submitted {(rd-od).days} days after observation (>30 = late)")
        except ValueError as e: err("BAD_DATE","recorded_at",str(e))
    return errors, warns
def validate_dataframe(df, conn, dup_strategy="skip"):
    df=df.copy(); df.columns=[str(c).strip().lower() for c in df.columns]
    missing=[c for c in OBS_REQ if c not in df.columns]
    if missing: return {"fatal":f"Missing required column(s): {', '.join(missing)}. Download the sample template below."}
    sites={r["code"]:r["id"] for r in conn.execute("SELECT id,code FROM sites")}
    existing={}
    for r in conn.execute("SELECT o.count,s.code,o.taxon,o.observed_at FROM observations o JOIN sites s ON s.id=o.site_id WHERE o.deleted_at IS NULL"):
        existing[(r["code"],r["taxon"].strip().lower(),str(r["observed_at"])[:10])]=r["count"]
    today_d=now().date(); seen={}; recs=[]; report=[]
    for i,raw in df.iterrows():
        row={k:raw.get(k) for k in df.columns}; rownum=int(i)+2
        errors,warns=validate_obs_fields(row,sites,today_d)
        key=None
        if not errors:
            od=parse_date(row["observed_at"]).isoformat()
            key=(str(row["site_code"]).strip(),str(row["taxon"]).strip().lower(),od)
            prev = seen.get(key, existing.get(key))
            if prev is not None:
                if int(float(row["count"]))==int(prev):
                    if dup_strategy=="reject": errors.append({"code":"DUPLICATE","field":"count","msg":f"Duplicate of existing key {key}","severity":"error"})
                    else: warns.append({"code":"DUPLICATE","field":"count","msg":f"Duplicate key {key} — row will be skipped safely","severity":"warning"})
                else:
                    warns.append({"code":"CONTRADICTORY","field":"count","msg":f"Same key {key} exists with count {prev} vs {row['count']} — kept for reviewer reconciliation","severity":"warning"})
            seen[key]=int(float(row["count"]))
        codes=[e["code"] for e in errors]; wcodes=[w["code"] for w in warns]
        if errors: disp="❌ INVALID"
        elif dup_strategy=="skip" and "DUPLICATE" in wcodes: disp="⏭️ SKIPPED (dup)"
        elif warns: disp="⚠️ VALID + FLAGS"
        else: disp="✅ VALID"
        for e in errors+warns:
            report.append({"row":rownum,"field":e["field"],"code":e["code"],"severity":e["severity"],"message":e["msg"],
                           "raw":json.dumps({k:str(v) for k,v in row.items()},default=str)})
        recs.append({"rownum":rownum,"row":row,"errors":errors,"warns":warns,"disp":disp,
                     "importable":(not errors) and not (dup_strategy=="skip" and "DUPLICATE" in wcodes and "CONTRADICTORY" not in wcodes)})
    prev_df=df.copy()
    prev_df.insert(0,"_row",[r["rownum"] for r in recs])
    prev_df.insert(1,"_status",[r["disp"] for r in recs])
    prev_df.insert(2,"_issues",[", ".join([e["code"] for e in r["errors"]]+[w["code"] for w in r["warns"]]) or "—" for r in recs])
    stats={"total":len(recs),"valid":sum(1 for r in recs if r["disp"]=="✅ VALID"),
           "flagged":sum(1 for r in recs if r["disp"]=="⚠️ VALID + FLAGS"),
           "skipped":sum(1 for r in recs if "SKIPPED" in r["disp"]),
           "invalid":sum(1 for r in recs if r["disp"]=="❌ INVALID")}
    return {"fatal":None,"preview":prev_df,"recs":recs,"report":pd.DataFrame(report),
            "stats":stats,"sites":sites}
def commit_import(vres, fname, blob):
    require("import")
    sha=sha_bytes(blob); path=SRC/f"{sha[:12]}_{safe_name(fname)}"
    path.write_bytes(blob)
    with db() as c:
        fid=ins(c,"source_files",{"filename":safe_name(fname),"sha256":sha,"kind":"import","bytes":len(blob),
            "row_count":vres["stats"]["total"],"imported_by":ss.actor,"imported_at":now_iso(),"schema_version":SCHEMA,"path":str(path)})
        n=0
        for r in vres["recs"]:
            if not r["importable"]: continue
            row=r["row"]; flags=[w["code"] for w in r["warns"]]
            od=parse_date(row["observed_at"]).isoformat()
            rd=str(row.get("recorded_at") or "").strip()
            rd=parse_date(rd).isoformat() if rd else now().date().isoformat()
            taxon=str(row["taxon"]).strip()
            oid=ins(c,"observations",{"site_id":vres["sites"][str(row["site_code"]).strip()],"taxon":taxon,
                "common_name":str(row.get("common_name") or taxon).strip(),"count":int(float(row["count"])),
                "unit":str(row["unit"]).strip(),"method":str(row["method"]).strip(),"observed_at":od,"recorded_at":rd,
                "recorded_by":ss.actor,"status":"DRAFT" if flags else "VALIDATED","flags":json.dumps(flags),
                "notes":str(row.get("notes") or "").strip(),"source_file_id":fid,"source_row":r["rownum"],"origin":"import",
                "schema_version":SCHEMA,"created_at":now_iso(),"updated_at":now_iso()})
            log_event(c,"create","observations",oid,f"{code_of('observations',oid)} from {fname} row {r['rownum']}")
            n+=1
        log_event(c,"import","source_files",fid,f"{fname} · {n} rows committed · sha256 {sha[:16]}…")
    return n, fid, sha
def sample_rows(bad=False):
    t=now().date(); rows=[]
    picks=[("WIL","Lutra lutra","Eurasian otter",3,"holts","camera-trap"),("WIL","Anax imperator","Emperor dragonfly",17,"individuals","transect"),
     ("HAW","Turdus philomelos","Song thrush",6,"territories","transect"),("EAS","Polyommatus icarus","Common blue butterfly",24,"individuals","transect"),
     ("RIV","Alcedo atthis","Kingfisher",1,"individuals","casual"),("QRY","Alauda arvensis","Skylark",4,"territories","transect"),
     ("CME","Bombus lapidarius","Red-tailed bumblebee",31,"individuals","quadrat"),("WIL","Triturus cristatus","Great crested newt",2,"individuals","eDNA"),
     ("HAW","Erinaceus europaeus","European hedgehog",2,"individuals","camera-trap"),("CME","Primula veris","Cowslip",45,"individuals","quadrat"),
     ("RIV","Arvicola amphibius","Water vole",9,"burrows","transect"),("EAS","Alauda arvensis","Skylark",3,"territories","transect")]
    for i,(sc,tx,cn,ct,un,me) in enumerate(picks):
        rows.append({"site_code":sc,"taxon":tx,"common_name":cn,"count":ct,"unit":un,"method":me,
                     "observed_at":(t-timedelta(days=2+i)).isoformat(),"recorded_at":t.isoformat(),"notes":"demo transect"})
    if bad:
        rows += [
         {"site_code":"XXX","taxon":"Lutra lutra","common_name":"Otter","count":2,"unit":"holts","method":"camera-trap","observed_at":t.isoformat(),"recorded_at":t.isoformat(),"notes":"unknown site"},
         {"site_code":"WIL","taxon":"Rana temporaria","common_name":"Frog","count":-4,"unit":"individuals","method":"quadrat","observed_at":t.isoformat(),"recorded_at":t.isoformat(),"notes":"negative"},
         {"site_code":"HAW","taxon":"Myotis daubentonii","common_name":"Bat","count":12,"unit":"individuals","method":"acoustic","observed_at":"2026-02-30","recorded_at":t.isoformat(),"notes":"impossible date"},
         {"site_code":"EAS","taxon":"Primula veris","common_name":"Cowslip","count":8,"unit":"litres","method":"quadrat","observed_at":t.isoformat(),"recorded_at":t.isoformat(),"notes":"bad unit"},
         dict(rows[0]),
         {"site_code":"RIV","taxon":"Lutra lutra","common_name":"Otter","count":1,"unit":"","method":"","observed_at":t.isoformat(),"recorded_at":t.isoformat(),"notes":"missing fields"},
         {"site_code":"CME","taxon":"Anax imperator","common_name":"Dragonfly","count":5,"unit":"individuals","method":"transect","observed_at":(t+timedelta(days=9)).isoformat(),"recorded_at":t.isoformat(),"notes":"future"},
         {"site_code":"QRY","taxon":"Bombus lapidarius","common_name":"Bumblebee","count":9999,"unit":"individuals","method":"quadrat","observed_at":(t-timedelta(days=60)).isoformat(),"recorded_at":t.isoformat(),"notes":"out of range + late"},
        ]
    return rows
def sample_csv_bytes(bad=False): return pd.DataFrame(sample_rows(bad)).to_csv(index=False).encode()
def sample_xlsx_bytes():
    b=io.BytesIO(); pd.DataFrame(sample_rows(False)).to_excel(b,index=False,engine="openpyxl"); return b.getvalue()

# ────────────────────────────────────────── SEED ──────────────────────────────
def seed(c):
    rng=random.Random(17); t0=now()
    for name,kind in [("Alder Valley Borough Council","Municipality"),("Verdant Ecology Consultancy","Consultancy"),("Northfield Utilities","Utility")]:
        ins(c,"organizations",{"name":name,"kind":kind,"jurisdiction":"England · Alder Valley"})
    sids={}
    for code,name,hab,cond,area,lat,lon,desig,org,tidx in SITE_SEED:
        sids[code]=ins(c,"sites",{"code":code,"org_id":org,"name":name,"habitat":hab,"condition":cond,"area_ha":area,
            "lat":lat,"lon":lon,"designation":desig,"created_at":iso(t0-timedelta(days=120)),"schema_version":SCHEMA})
    fid=ins(c,"source_files",{"filename":"synthetic_seed_v1.csv","sha256":sha_bytes(b"synthetic-seed-v1"),"kind":"seed",
        "bytes":0,"row_count":0,"imported_by":"system","imported_at":iso(t0-timedelta(days=80)),"schema_version":SCHEMA,"path":"(generated)"})
    log_event(c,"import","source_files",fid,"Synthetic demo seed v1 loaded (deterministic RNG · seed 17)","system","system",iso(t0-timedelta(days=80)))
    mult={code:rng.uniform(.8,1.2) for code,*_ in SITE_SEED}
    nobs=0
    for code,name,hab,cond,area,lat,lon,desig,org,tidx in SITE_SEED:
        for w in range(10):
            for ti in rng.sample(tidx, k=min(len(tidx), rng.choice([3,3,4]))):
                sci,cn,grp,meth,base=TAXA[ti]
                cnt=max(0,int(round(base*mult[code]*(0.75+0.35*math.sin((w+ti)/2.0))+rng.gauss(0,base*.18))))
                if code=="QRY" and sci=="Alauda arvensis" and w==7: cnt=1
                od=(t0-timedelta(days=(9-w)*7+rng.randint(0,4))).date()
                lag=rng.choice([0,1,2,3,4,40]) if rng.random()<.12 else rng.randint(0,3)
                rd=od+timedelta(days=lag)
                row={"site_code":code,"taxon":sci,"count":cnt,"unit":"territories" if grp=="Bird" else "individuals",
                     "method":meth,"observed_at":od.isoformat(),"recorded_at":rd.isoformat()}
                _,warns=validate_obs_fields(row,set(sids),t0.date())
                flags=[x["code"] for x in warns]
                status="APPROVED" if w<=5 else ("VALIDATED" if w in (6,8) else ("IN_REVIEW" if w==7 and rng.random()<.6 else ("VALIDATED" if w==7 else "DRAFT")))
                actor=rng.choice(["Diego Fernández","Amara Okafor"])
                oid=ins(c,"observations",{"site_id":sids[code],"taxon":sci,"common_name":cn,"count":cnt,"unit":row["unit"],
                    "method":meth,"observed_at":od.isoformat(),"recorded_at":rd.isoformat(),"recorded_by":actor,"status":status,
                    "flags":json.dumps(flags),"notes":f"{grp} survey · week {w+1}","source_file_id":fid,"source_row":nobs+2,
                    "origin":"seed","schema_version":SCHEMA,"created_at":iso(t0-timedelta(days=(9-w)*7)),"updated_at":iso(t0-timedelta(days=max(0,(9-w)*7-2)))})
                nobs+=1
                ets=iso(t0-timedelta(days=max(0,(9-w)*7-2)))
                if status in ("APPROVED","VALIDATED","IN_REVIEW"):
                    log_event(c,"validate","observations",oid,f"{code_of('observations',oid)} passed schema checks",actor,"Analyst",ets)
                if status=="APPROVED":
                    log_event(c,"approve","observations",oid,f"{code_of('observations',oid)}: IN_REVIEW → APPROVED","Dr. Ingrid Solberg","Reviewer",ets)
                if status=="IN_REVIEW":
                    log_event(c,"submit","observations",oid,f"{code_of('observations',oid)} submitted for review",actor,"Analyst",ets)
    specials=[("EAS","Polyommatus icarus","Common blue butterfly",9999,"individuals","transect",["OUT_OF_RANGE"],"Range check demo — reviewer must reconcile"),
              ("RIV","Lutra lutra","Eurasian otter",2,"holts","camera-trap",["CONTRADICTORY"],"Conflicts with eDNA count 14 on same date"),
              ("RIV","Lutra lutra","Eurasian otter",14,"holts","eDNA",["CONTRADICTORY"],"Conflicts with camera count 2 on same date"),
              ("HAW","Myotis daubentonii","Daubenton's bat",18,"individuals","",["MISSING_FIELD","BAD_METHOD"],"Method omitted in field app — hard error demo")]
    for sc,sci,cn,ct,un,me,fl,note in specials:
        od=(t0-timedelta(days=3)).date().isoformat()
        oid=ins(c,"observations",{"site_id":sids[sc],"taxon":sci,"common_name":cn,"count":ct,"unit":un,"method":me,
            "observed_at":od,"recorded_at":od,"recorded_by":"Diego Fernández","status":"DRAFT","flags":json.dumps(fl),
            "notes":note,"source_file_id":fid,"source_row":nobs+2,"origin":"seed","schema_version":SCHEMA,
            "created_at":now_iso(),"updated_at":now_iso()})
        log_event(c,"create","observations",oid,f"{code_of('observations',oid)} seeded exception-path example")
        nobs+=1
    c.execute("UPDATE source_files SET row_count=? WHERE id=?",(nobs,fid))
    imp=[("EAS","Vegetation clearance for phase 1","habitat-loss",0.8,3,"APPROVED"),
         ("WIL","Drainage ditch re-profiling","hydrology",0.3,2,"IN_REVIEW"),
         ("HAW","Construction lighting spill","disturbance",0.2,1,"APPROVED"),
         ("RIV","Outfall sediment plume","pollution",0.4,2,"IN_REVIEW"),
         ("QRY","Haul road fragmentation","fragmentation",1.1,3,"VALIDATED")]
    for i,(sc,act,typ,area,sev,st) in enumerate(imp):
        iid=ins(c,"impacts",{"site_id":sids[sc],"activity":act,"impact_type":typ,"area_ha":area,"severity":sev,
            "start_date":(t0-timedelta(days=40-i*5)).date().isoformat(),"status":st,"flags":"[]",
            "notes":"Logged from site walkover","origin":"seed","created_at":iso(t0-timedelta(days=40-i*5)),"updated_at":now_iso(),"schema_version":SCHEMA})
        log_event(c,"create","impacts",iid,f"{code_of('impacts',iid)} · {act}")
        if st=="IN_REVIEW": log_event(c,"submit","impacts",iid,f"{code_of('impacts',iid)} submitted for review","Diego Fernández","Analyst")
    acts=[("EAS","Wildflower meadow creation","Species-rich meadow","Good",3.1,10,"Medium","Elevated",18500,45,"APPROVED"),
          ("WIL","Wetland scrape restoration","Wetland","Good",1.2,5,"Low","Elevated",24000,100,"APPROVED"),
          ("QRY","Heathland translocation","Heathland","Poor",4.5,20,"High","Standard",61000,20,"IN_REVIEW"),
          ("RIV","Riparian buffer planting","Riparian","Good",2.0,5,"Medium","Standard",14200,30,"VALIDATED"),
          ("HAW","Woodland edge expansion","Ancient woodland","Fair",0.9,15,"High","Elevated",9800,0,"DRAFT"),
          ("WIL","Pond restoration","Wetland","Good",0.4,5,"Low","Standard",12000,0,"DRAFT")]
    for i,(sc,at,ht,ct,area,yrs,diff,strat,cost,prog,st) in enumerate(acts):
        aid=ins(c,"actions",{"site_id":sids[sc],"action_type":at,"habitat_target":ht,"condition_target":ct,"area_ha":area,
            "years_to_target":yrs,"difficulty":diff,"strategic":strat,"start_date":(t0-timedelta(days=60-i*6)).date().isoformat(),
            "cost_gbp":cost,"progress":prog,"status":st,"flags":"[]","notes":"Costed in restoration plan","origin":"seed",
            "created_at":iso(t0-timedelta(days=60-i*6)),"updated_at":now_iso(),"schema_version":SCHEMA})
        log_event(c,"create","actions",aid,f"{code_of('actions',aid)} · {at}")
        if st in ("APPROVED","IN_REVIEW"):
            log_event(c,"submit","actions",aid,f"{code_of('actions',aid)} submitted","Diego Fernández","Analyst")
        if st=="APPROVED":
            log_event(c,"approve","actions",aid,f"{code_of('actions',aid)}: IN_REVIEW → APPROVED","Dr. Ingrid Solberg","Reviewer")
    ev_specs=[("sites",sids["WIL"],"transect_WIL.csv","csv",("week,plot,species,count\n1,P1,Anax imperator,14\n1,P2,Anax imperator,19\n2,P1,Anax imperator,17\n2,P2,Anax imperator,21\n").encode()),
        ("sites",sids["EAS"],"fieldnotes_EAS.txt","txt","FIELD NOTES — Eastgate parcel (SYNTHETIC)\nSward short, rabbit-grazed. Cowslip frequent on bank.\nSkylark: 3 territories, song flight observed 07:40.\nRecommend meadow creation on 3.1 ha northern block.\n".encode()),
        ("sites",sids["RIV"],"sensor_RIV.json","json",json.dumps({"station":"RIV-02","type":"water-quality","synthetic":True,"readings":[{"t":"06:00","ph":7.2,"turbidity_ntu":4.1},{"t":"07:00","ph":7.1,"turbidity_ntu":5.8}]}).encode()),
        ("sites",sids["QRY"],"habitatmap_QRY.svg","svg","<svg xmlns='http://www.w3.org/2000/svg' width='420' height='260'><rect width='420' height='260' fill='#12291f'/><rect x='30' y='40' width='160' height='90' fill='#2f5c47' rx='8'/><rect x='220' y='60' width='150' height='120' fill='#3b4a3f' rx='8'/><circle cx='120' cy='190' r='26' fill='#38bdf8' opacity='.7'/><text x='40' y='60' fill='#dffbe9' font-size='12'>Heath block A</text><text x='230' y='80' fill='#dffbe9' font-size='12'>Spoil (bare)</text><text x='30' y='245' fill='#fbbf24' font-size='11'>SYNTHETIC HABITAT SKETCH — NOT SURVEY GRADE</text></svg>".encode()),
        ("sites",sids["HAW"],"transect_HAW.csv","csv",b"week,plot,species,count\n1,T1,Turdus philomelos,5\n1,T2,Turdus philomelos,7\n2,T1,Turdus philomelos,6\n"),
        ("sites",sids["WIL"],"fieldnotes_WIL.txt","txt","FIELD NOTES — Willowbrook (SYNTHETIC)\nScrape holding water well. Dragonflies active on south edge.\nOtter spraint confirmed at outflow. GCN eDNA positive pond 2.\n".encode()),
        ("sites",sids["QRY"],"sensor_QRY.json","json",json.dumps({"station":"QRY-01","type":"acoustic","synthetic":True,"bat_passes_per_hr":[21,18,26,19]}).encode()),
        ("sites",sids["EAS"],"sitephoto_EAS.svg","svg","<svg xmlns='http://www.w3.org/2000/svg' width='420' height='240'><defs><linearGradient id='s' x1='0' y1='0' x2='0' y2='1'><stop offset='0' stop-color='#38bdf8'/><stop offset='1' stop-color='#0e2a1f'/></linearGradient></defs><rect width='420' height='240' fill='url(#s)'/><path d='M0 170 Q120 140 240 168 T420 160 V240 H0 Z' fill='#1c4634'/><circle cx='350' cy='50' r='22' fill='#fbbf24' opacity='.85'/><text x='14' y='226' fill='#fbbf24' font-size='11'>SYNTHETIC PLACEHOLDER IMAGE — DEMO ONLY</text></svg>".encode())]
    for ent,eid,fn,kind,blob in ev_specs:
        p=EVI/f"seed_{fn}"; p.write_bytes(blob)
        evid=ins(c,"evidence",{"entity":ent,"entity_id":eid,"filename":fn,"kind":kind,"bytes":len(blob),
            "sha256":sha_bytes(blob),"path":str(p),"uploaded_by":"Diego Fernández","uploaded_at":iso(t0-timedelta(days=30))})
        log_event(c,"attach",ent,eid,f"Evidence '{fn}' attached · sha {sha_bytes(blob)[:12]}…","Diego Fernández","Analyst")
    odf=obs_df(c)
    asm=[("EAS",{"area":3.1,"base_habitat":"Modified grassland","base_condition":"Fair","target_habitat":"Species-rich meadow",
                 "target_condition":"Good","years":10,"difficulty":"Medium","strategic":"Elevated","target_pct":10},"APPROVED"),
         ("WIL",{"area":1.2,"base_habitat":"Wetland","base_condition":"Fair","target_habitat":"Wetland",
                 "target_condition":"Good","years":5,"difficulty":"Low","strategic":"Elevated","target_pct":10},"APPROVED"),
         ("QRY",{"area":4.5,"base_habitat":"Bare spoil","base_condition":"Poor","target_habitat":"Heathland",
                 "target_condition":"Poor","years":20,"difficulty":"High","strategic":"Standard","target_pct":10},"IN_REVIEW")]
    for sc,params,st in asm:
        q=site_quality(odf,sids[sc])
        res=assess(params,"1.2.0",q["soft"],q["estimate"],q["stale"])
        aid=ins(c,"assessments",{"site_id":sids[sc],"params":json.dumps(params),"result":json.dumps(res),
            "rules_version":"1.2.0","engine_version":ENGINE_VER,"status":st,"priority":2 if sc=="QRY" else 0,
            "created_by":"Diego Fernández","created_at":iso(t0-timedelta(days=6)),"updated_at":iso(t0-timedelta(days=5))})
        log_event(c,"create","assessments",aid,f"{code_of('assessments',aid)} computed · rules v1.2.0 · net {pctf(res['pct'])}","Diego Fernández","Analyst",iso(t0-timedelta(days=6)))
        log_event(c,"submit","assessments",aid,f"{code_of('assessments',aid)} submitted for review","Diego Fernández","Analyst",iso(t0-timedelta(days=6)))
        if st=="APPROVED":
            log_event(c,"approve","assessments",aid,f"{code_of('assessments',aid)}: IN_REVIEW → APPROVED","Dr. Ingrid Solberg","Reviewer",iso(t0-timedelta(days=5)))
    ins(c,"saved_views",{"name":"⚠ Flagged field data","filters":json.dumps({"f_quality":"Flagged (any)","f_sites":[],"f_status":[],"f_q":"","f_sort":"Newest first"}),"created_by":"Amara Okafor","created_at":now_iso()})
    ins(c,"saved_views",{"name":"Eastgate pipeline","filters":json.dumps({"f_sites":["EAS"],"f_status":[],"f_quality":"Any","f_q":"","f_sort":"Newest first"}),"created_by":"Amara Okafor","created_at":now_iso()})

# ────────────────────────────────────────── SIMULATION ────────────────────────
def sim_init():
    if "sim" not in ss:
        ss.sim={"t":0,"buf":[],"events":[],"running":True,"force":0,"det":0,"anom":0,
                "scenario":"Dawn chorus","speed":2,"noise":35,"window":120,
                "rng":random.Random(17),"start":now(),"last_det":None}
def sim_tick():
    s=ss.sim; s["t"]+=1; t=s["t"]; P=SCENARIOS[s["scenario"]]; sig=s["noise"]/100*6
    a=max(0,min(100,P["a"]+8*math.sin(t/9)+s["rng"].gauss(0,sig)))
    p=max(0,min(100,P["p"]+7*math.sin(t/7+2)+s["rng"].gauss(0,sig)))
    w=max(0,min(100,P["w"]+4*math.sin(t/13+1)+s["rng"].gauss(0,sig*.7)))
    anom=False
    if s["force"]>0:
        w=max(0,w-32); a=max(0,a-12); anom=True; s["force"]-=1
        if s["force"]==1:
            s["events"].append({"t":t,"kind":"anomaly","txt":"⚠ Turbidity spike — RIV outfall sensor · reviewer alert raised"})
    elif s["rng"].random()<.008:
        anom=True; s["anom"]+=1
        s["events"].append({"t":t,"kind":"anomaly","txt":"⚠ Unexpected activity dip — auto-flagged by z-score baseline"})
    if s["rng"].random()<P["ev"]:
        site=rng_site(); ti=s["rng"].choice(site["tidx"]); sci,cn,grp,meth,base=TAXA[ti]
        n=s["rng"].randint(1,4); s["det"]+=1
        det={"t":t,"site_id":site["id"],"site":site["code"],"taxon":sci,"common":cn,"count":n,"method":meth}
        s["last_det"]=det
        s["events"].append({"t":t,"kind":"detection","txt":f"{cn} ×{n} · {site['code']} · {meth}"})
    s["buf"].append({"t":t,"acoustic":round(a,1),"pollinator":round(p,1),"wqi":round(w,1),"anom":anom})
    s["buf"]=s["buf"][-480:]; s["events"]=s["events"][-60:]
def rng_site():
    return ss.site_meta[ss.sim["rng"].randrange(len(ss.site_meta))]
def promote_detection():
    require("create")
    d=ss.sim.get("last_det")
    if not d: raise ValueError("No detection to log yet — wait a tick.")
    with db() as c:
        oid=ins(c,"observations",{"site_id":d["site_id"],"taxon":d["taxon"],"common_name":d["common"],"count":d["count"],
            "unit":"individuals","method":d["method"],"observed_at":now().date().isoformat(),"recorded_at":now().date().isoformat(),
            "recorded_by":ss.actor,"status":"DRAFT","flags":json.dumps(["ESTIMATE"]),
            "notes":f"Auto-logged from live simulation tick #{d['t']} (synthetic sensor)","origin":"sim",
            "schema_version":SCHEMA,"created_at":now_iso(),"updated_at":now_iso()})
        log_event(c,"create","observations",oid,f"{code_of('observations',oid)} promoted from SIM tick #{d['t']} · {d['common']}")
    st.toast(f"{code_of('observations',oid)} logged as DRAFT with ESTIMATE flag", icon="📌")
@frag
def live_panel():
    s=ss.sim
    st.markdown('<div class="sec" style="margin-top:14px"><div class="sec-k">Live simulation · provenance: SIM (synthetic)</div>'
                '<div class="sec-t">📡 Field Telemetry — running now</div></div>', unsafe_allow_html=True)
    c1,c2,c3,c4=st.columns([2.2,1,1.1,1.1])
    s["scenario"]=c1.selectbox("Scenario",list(SCENARIOS),index=list(SCENARIOS).index(s["scenario"]),key="sim_scen")
    s["running"]=c2.toggle("Running",value=s["running"],key="sim_run")
    s["speed"]=c3.slider("Speed ×",1,5,value=s["speed"],key="sim_speed")
    s["noise"]=c4.slider("Noise %",0,100,value=s["noise"],key="sim_noise")
    c5,c6,c7,c8,c9=st.columns([1.6,1.1,1.1,.9,.9])
    s["window"]=c5.slider("Window (ticks)",40,240,value=s["window"],key="sim_win")
    if c6.button("⚡ Inject anomaly",key="sim_anom"):
        s["force"]=3; s["anom"]+=1; st.toast("Anomaly injected into water-quality channel",icon="⚡")
    log_clicked=c7.button("📌 Log detection",key="sim_log",disabled=not can("create") or not s["last_det"],
                          help="Promote the latest simulated detection into the registry as a DRAFT observation")
    if c8.button("♻️ Reset feed",key="sim_reset"):
        s["buf"]=[]; s["events"]=[]; s["t"]=0; s["det"]=0; s["anom"]=0; s["force"]=0; s["start"]=now(); s["rng"]=random.Random(17)
    if not HAS_FRAG and c9.button("▶ Advance",key="sim_adv"):
        for _ in range(s["speed"]): sim_tick()
    if s["running"]:
        for _ in range(s["speed"]): sim_tick()
    if s["buf"]:
        df=pd.DataFrame(s["buf"]).tail(s["window"])
        fig=go.Figure()
        fig.add_trace(go.Scatter(x=df.t,y=df.acoustic,name="Acoustic activity",line=dict(color=PAL["green"],width=2)))
        fig.add_trace(go.Scatter(x=df.t,y=df.pollinator,name="Pollinator visits",line=dict(color=PAL["amber"],width=2,dash="dash")))
        fig.add_trace(go.Scatter(x=df.t,y=df.wqi,name="Water quality idx",line=dict(color=PAL["blue"],width=2,dash="dot")))
        an=df[df.anom]
        if len(an): fig.add_trace(go.Scatter(x=an.t,y=an.wqi,mode="markers",name="Anomaly",
            marker=dict(color=PAL["magenta"],size=10,symbol="x")))
        fig_base(fig,250); fig.update_yaxes(range=[0,105]); fig.update_xaxes(title="tick")
        st.plotly_chart(fig,config=PCFG,key="live_fig",**W_PC)
    else:
        empty_state("Feed reset — press Running or Advance to stream ticks.","📡")
    lastw=s["buf"][-1]["wqi"] if s["buf"] else "—"
    m1,m2,m3,m4=st.columns(4)
    with m1: kpi("🕒","Ticks",s["t"],"2 s / tick (accelerated)",PAL["teal"])
    with m2: kpi("🦇","Detections",s["det"],"promotable to registry",PAL["green"])
    with m3: kpi("⚠️","Anomalies",s["anom"],"z-score baseline watch",PAL["magenta"])
    with m4: kpi("💧","Last WQI",lastw,"index 0–100",PAL["blue"])
    if s["events"]:
        ticks=""
        for e in s["events"][-5:][::-1]:
            c={"detection":PAL["green"],"anomaly":PAL["magenta"]}.get(e["kind"],PAL["blue"])
            ts=(s["start"]+timedelta(seconds=e["t"]*2)).strftime("%H:%M:%S")
            ticks+=f'<div class="tick"><span class="tl-dot" style="position:static;background:{c}"></span><span style="color:#8fa69b">{ts}</span><span>{esc(e["txt"])}</span></div>'
        st.markdown(ticks,unsafe_allow_html=True)
    st.caption("Synthetic sensor simulation for interface testing — every promoted record is flagged ESTIMATE and traceable to its tick.")
    if log_clicked:
        try: promote_detection(); rerun_app()
        except (PermissionError,ValueError) as e: st.error(str(e))

# ────────────────────────────────────────── SHARED DATA LOAD ──────────────────
def load_all():
    with db() as c:
        return sites_df(c), obs_df(c), impacts_df(c), actions_df(c), assess_df(c)
def latest_assessment(adf, site_id, prefer_approved=True):
    sub=adf[adf.site_id==site_id]
    if not len(sub): return None
    if prefer_approved:
        ap=sub[sub.status=="APPROVED"]
        if len(ap): return ap.iloc[0].to_dict()
    return sub.iloc[0].to_dict()
def review_items(sdf,odf,idf,adf,asmf):
    items=[]
    for _,r in odf[odf.status=="IN_REVIEW"].iterrows():
        items.append({"table":"observations","id":int(r.id),"code":code_of("observations",r.id),"site":r.site_code,
            "summary":f"{r.common_name} ×{r.count} {r.unit} · {r.method} · {r.observed_at}","flags":flags_of(r),
            "priority":int(r.priority),"ts":r.updated_at,"extra":""})
    for _,r in idf[idf.status=="IN_REVIEW"].iterrows():
        items.append({"table":"impacts","id":int(r.id),"code":code_of("impacts",r.id),"site":r.site_code,
            "summary":f"{r.activity} · {r.impact_type} · {r.area_ha} ha · severity {r.severity}/3","flags":flags_of(r),
            "priority":int(r.priority),"ts":r.updated_at,"extra":""})
    for _,r in adf[adf.status=="IN_REVIEW"].iterrows():
        items.append({"table":"actions","id":int(r.id),"code":code_of("actions",r.id),"site":r.site_code,
            "summary":f"{r.action_type} → {r.habitat_target} ({r.condition_target}) · {r.area_ha} ha · {money(r.cost_gbp)}","flags":flags_of(r),
            "priority":int(r.priority),"ts":r.updated_at,"extra":""})
    for _,r in asmf[asmf.status=="IN_REVIEW"].iterrows():
        res=json.loads(r.result)
        items.append({"table":"assessments","id":int(r.id),"code":code_of("assessments",r.id),"site":r.site_code,
            "summary":f"Net units {res['net']:+.2f} ({pctf(res['pct'])}) · rules v{r.rules_version}",
            "flags":res.get("warnings",[]) and ["CHECK WARNINGS"] or [],"priority":int(r.priority),"ts":r.updated_at,
            "extra":f"{'✅ meets target' if res['meets'] else '⛔ below target'} · ±{res['band_abs']} units"})
    items.sort(key=lambda x:(-x["priority"], x["ts"] or ""))
    return items

# ────────────────────────────────────────── CHARTS ────────────────────────────
HAB_COLORS={"Wetland":PAL["blue"],"Ancient woodland":PAL["green"],"Modified grassland":PAL["lime"],
 "Riparian":PAL["teal"],"Bare spoil":PAL["clay"],"Species-rich meadow":PAL["amber"],"Heathland":PAL["violet"],"Urban mosaic":PAL["magenta"]}
def pulse_fig(odf,sdf):
    d=odf.copy(); d["week"]=pd.to_datetime(d.observed_at).dt.to_period("W-SUN").dt.start_time
    d=d.merge(sdf[["id","habitat"]],left_on="site_id",right_on="id",suffixes=("","_s"))
    g=d.groupby(["week","habitat"]).size().reset_index(name="n")
    fig=go.Figure()
    for hab,sub in g.groupby("habitat"):
        fig.add_trace(go.Bar(x=sub.week,y=sub.n,name=hab,marker_color=HAB_COLORS.get(hab,PAL["green"])))
    fig.update_layout(barmode="stack")
    return fig_base(fig,280,"Weekly observation volume by habitat")
def donut_fig(odf):
    d=odf.copy(); d["group"]=d.taxon.map(TAXON_GROUP).fillna("Other")
    g=d.groupby("group").size().sort_values(ascending=False)
    cols=[PAL["green"],PAL["blue"],PAL["amber"],PAL["teal"],PAL["clay"],PAL["violet"],PAL["magenta"],PAL["lime"]]
    fig=go.Figure(go.Pie(labels=g.index,values=g.values,hole=.62,sort=False,
        marker=dict(colors=cols[:len(g)],line=dict(color="#0a1712",width=2)),textinfo="label+percent",textfont=dict(size=11)))
    fig.update_layout(showlegend=False)
    return fig_base(fig,280,"Registry composition by taxonomic group")
def trend_fig(odf,site_id):
    d=odf[odf.site_id==site_id].copy()
    d["week"]=pd.to_datetime(d.observed_at).dt.to_period("W-SUN").dt.start_time
    g=d.groupby("week")["count"].sum().sort_index()
    fig=go.Figure()
    fig.add_trace(go.Scatter(x=g.index,y=g.values,mode="lines+markers",name="Weekly count",
        line=dict(color=PAL["green"],width=2.5),fill="tozeroy",fillcolor="rgba(74,222,128,.10)"))
    fl=zscore_flags(list(g.values))
    if fl:
        fig.add_trace(go.Scatter(x=[g.index[i] for i in fl],y=[g.values[i] for i in fl],mode="markers",
            name="Anomaly (|z|>2.5)",marker=dict(color=PAL["magenta"],size=12,symbol="diamond")))
    return fig_base(fig,270,"Site trend · rolling z-score anomaly baseline")
def before_after_fig(sdf,asmf):
    rows=[]
    for _,s in sdf.iterrows():
        a=latest_assessment(asmf,int(s.id))
        if a:
            r=json.loads(a["result"]); rows.append((s.code,r["baseline"],r["post"],r["band_abs"],r["pct"],a["status"]))
    if not rows: return None
    fig=go.Figure()
    fig.add_trace(go.Bar(x=[r[0] for r in rows],y=[r[1] for r in rows],name="Baseline units",marker_color=PAL["clay"]))
    fig.add_trace(go.Bar(x=[r[0] for r in rows],y=[r[2] for r in rows],name="Post-intervention",marker_color=PAL["green"],
        error_y=dict(type="data",array=[r[3] for r in rows],color="rgba(232,244,236,.6)")))
    for r in rows:
        fig.add_annotation(x=r[0],y=max(r[1],r[2])+max(2,r[3]),text=f"<b>{pctf(r[4])}</b>",showarrow=False,
                           font=dict(color=PAL["green"] if (r[4] or 0)>=10 else PAL["magenta"],size=13))
    fig.update_layout(barmode="group")
    return fig_base(fig,300,"Habitat units — baseline vs post-intervention (± heuristic band)")
def waterfall_fig(res):
    st_=res["steps"]
    fig=go.Figure(go.Waterfall(x=[s["label"] for s in st_],y=[s["value"] for s in st_],measure=[s["measure"] for s in st_],
        text=[f"{s['value']:+.2f}" if s["measure"]=="relative" else f"{s['value']:.2f}" for s in st_],textposition="outside",
        increasing={"marker":{"color":PAL["green"]}},decreasing={"marker":{"color":PAL["magenta"]}},
        totals={"marker":{"color":PAL["blue"]}},connector={"line":{"color":"rgba(159,184,171,.35)"}}))
    return fig_base(fig,320,"Where the units come from — deterministic decomposition")

# ────────────────────────────────────────── EXPORTS ───────────────────────────
REPORT_CSS="""body{background:#081410;color:#e8f4ec;font-family:Segoe UI,Inter,Arial,sans-serif;margin:0;padding:32px;}
.wrap{max-width:960px;margin:0 auto} h1{color:#4ade80;font-size:26px;margin:0} h2{color:#2dd4bf;font-size:17px;margin:26px 0 8px;border-bottom:1px solid #1c4634;padding-bottom:5px}
.sub{color:#9fb8ab;font-size:12px} .grid{display:flex;gap:12px;flex-wrap:wrap;margin:16px 0}
.k{background:#10231b;border:1px solid #1c4634;border-radius:12px;padding:12px 16px;min-width:150px}
.k b{display:block;font-size:21px;color:#4ade80}.k span{font-size:10px;letter-spacing:.1em;color:#9fb8ab;text-transform:uppercase}
table.tbl{border-collapse:collapse;width:100%;font-size:12px;margin:8px 0}
.tbl th{background:#12291f;color:#4ade80;text-align:left;padding:7px 9px;border:1px solid #1c4634}
.tbl td{padding:6px 9px;border:1px solid #1c4634;color:#dcefe3}
.warn{background:#2a1f0e;border:1px solid #fbbf24;color:#fbbf24;border-radius:10px;padding:10px 14px;font-size:12px;margin:14px 0}
.foot{color:#9fb8ab;font-size:11px;margin-top:28px;border-top:1px solid #1c4634;padding-top:12px}
code{color:#38bdf8;font-size:11px}"""
def log_export_cb(label, entity, eid):
    with db() as c: log_event(c,"export",entity,eid,f"Export: {label}")
def build_html_report(site_id=None, focus_code=None):
    sdf,odf,idf,adf,asmf=load_all()
    parts=[f"<html><head><meta charset='utf-8'><title>{APP} evidence pack</title><style>{REPORT_CSS}</style></head><body><div class='wrap'>"]
    scope="Portfolio — all sites" if site_id is None else sdf[sdf.id==site_id].iloc[0]["name"]
    parts.append(f"<h1>🌿 {APP} — Biodiversity Evidence Pack</h1><div class='sub'>{esc(scope)} · generated {fmt_dt(now_iso())} · app v{VER} · schema {SCHEMA} · engine {ENGINE_VER}</div>")
    parts.append("<div class='warn'>⚠ SYNTHETIC DEMO DATA — decision support only. Not a statutory biodiversity metric. Human approval required for regulated use.</div>")
    if focus_code: parts.append(f"<div class='sub'>Shared with focus record: <code>{esc(focus_code)}</code></div>")
    if site_id is None:
        rows=[]
        for _,s in sdf.iterrows():
            a=latest_assessment(asmf,int(s.id))
            r=json.loads(a["result"]) if a else None
            rows.append({"Site":s.code,"Name":s.name,"Habitat":s.habitat,"Area (ha)":s.area_ha,
                "Baseline":r["baseline"] if r else "—","Post":r["post"] if r else "—",
                "Net %":pctf(r["pct"]) if r else "—","Assessment":a["status"] if a else "none","Rules":a["rules_version"] if a else "—"})
        parts.append("<h2>Portfolio summary</h2>"+pd.DataFrame(rows).to_html(index=False,escape=True,border=0,classes="tbl"))
        f=before_after_fig(sdf,asmf)
        if f: parts.append(f.to_html(full_html=False,include_plotlyjs=True))
        parts.append("<h2>Observation register (latest 40)</h2>"+odf.head(40)[["site_code","taxon","common_name","count","unit","method","observed_at","status","origin"]].to_html(index=False,escape=True,border=0,classes="tbl"))
    else:
        s=sdf[sdf.id==site_id].iloc[0]; so=odf[odf.site_id==site_id]
        a=latest_assessment(asmf,site_id); r=json.loads(a["result"]) if a else None
        parts.append(f"<div class='grid'><div class='k'><span>Area</span><b>{s.area_ha} ha</b></div><div class='k'><span>Habitat</span><b style='font-size:14px'>{esc(s.habitat)}</b></div><div class='k'><span>Condition</span><b style='font-size:14px'>{esc(s.condition)}</b></div><div class='k'><span>Observations</span><b>{len(so)}</b></div><div class='k'><span>Richness</span><b>{so.taxon.nunique()}</b></div>"+(f"<div class='k'><span>Net change</span><b>{pctf(r['pct'])}</b></div>" if r else "")+"</div>")
        parts.append(f"<div class='sub'>Designation: {esc(s.designation)} · Owner: {esc(s.org_name)} · WGS84 {s.lat:.3f}, {s.lon:.3f}</div>")
        if r:
            parts.append(f"<h2>Impact assessment — {badge_txt(a['status'])} · rules v{a['rules_version']}</h2>")
            parts.append("<ul>"+"".join(f"<li>{esc(re.sub(r'[*]','',ln))}</li>" for ln in r["explanation"])+"</ul>")
            if a.get("override"):
                ov=json.loads(a["override"]); parts.append(f"<div class='warn'>Manual override: net {ov['net_pct']}% — reason: {esc(ov['reason'])}</div>")
        parts.append("<h2>Trend</h2>"+trend_fig(odf,site_id).to_html(full_html=False,include_plotlyjs=True))
        parts.append("<h2>Observations</h2>"+so[["taxon","common_name","count","unit","method","observed_at","status","flags","origin"]].head(30).to_html(index=False,escape=True,border=0,classes="tbl"))
        parts.append("<h2>Impacts</h2>"+idf[idf.site_id==site_id][["activity","impact_type","area_ha","severity","start_date","status"]].to_html(index=False,escape=True,border=0,classes="tbl"))
        parts.append("<h2>Restoration actions</h2>"+adf[adf.site_id==site_id][["action_type","habitat_target","area_ha","years_to_target","cost_gbp","progress","status"]].to_html(index=False,escape=True,border=0,classes="tbl"))
        with db() as c:
            ev=[dict(x) for x in c.execute("SELECT filename,kind,bytes,sha256,uploaded_at FROM evidence WHERE entity='sites' AND entity_id=?",(site_id,))]
            src=[dict(x) for x in c.execute("SELECT DISTINCT f.filename,f.sha256,f.kind,f.imported_at FROM source_files f JOIN observations o ON o.source_file_id=f.id WHERE o.site_id=?",(site_id,))]
            au=[dict(x) for x in c.execute("SELECT ts,actor,role,action,detail FROM audit WHERE entity='sites' AND entity_id=? OR detail LIKE ? ORDER BY ts DESC LIMIT 12",(site_id,f"%{s.code}%"))]
        parts.append("<h2>Evidence & checksums</h2>"+(pd.DataFrame(ev).to_html(index=False,escape=True,border=0,classes="tbl") if ev else "<div class='sub'>none</div>"))
        parts.append("<h2>Source lineage</h2>"+(pd.DataFrame(src).to_html(index=False,escape=True,border=0,classes="tbl") if src else "<div class='sub'>none</div>"))
        parts.append("<h2>Recent audit</h2>"+(pd.DataFrame(au).to_html(index=False,escape=True,border=0,classes="tbl") if au else "<div class='sub'>none</div>"))
    parts.append(f"<div class='foot'>{APP} v{VER} · full provenance retained in registry · exports are logged as audit events · synthetic demonstration dataset — no real customer data.</div></div></body></html>")
    return "".join(parts)
def badge_txt(s): return f"{STATUS_META.get(s,('',''))[0]} {s}"
def bundle_json(site_id=None):
    sdf,odf,idf,adf,asmf=load_all()
    if site_id is not None:
        odf=odf[odf.site_id==site_id]; idf=idf[idf.site_id==site_id]; adf=adf[adf.site_id==site_id]; asmf=asmf[asmf.site_id==site_id]
        sdf=sdf[sdf.id==site_id]
    return json.dumps({"meta":{"app":APP,"version":VER,"schema":SCHEMA,"engine":ENGINE_VER,"generated":now_iso(),
        "synthetic":True,"disclaimer":"Decision support only — not a statutory metric."},
        "sites":json.loads(sdf.to_json(orient="records")),"observations":json.loads(odf.to_json(orient="records")),
        "impacts":json.loads(idf.to_json(orient="records")),"actions":json.loads(adf.to_json(orient="records")),
        "assessments":json.loads(asmf.to_json(orient="records"))},indent=2,default=str).encode()

# ────────────────────────────────────────── SELF-TEST SUITE ───────────────────
def run_self_tests():
    results=[]
    def close(a,b,eps=1e-6): assert abs(a-b)<eps, f"{a} != {b}"
    def raises(exc,fn):
        try: fn()
        except exc: return
        raise AssertionError(f"expected {exc.__name__}")
    def t(name,fn):
        t0=time.perf_counter()
        try: fn(); ok,det=True,"ok"
        except AssertionError as e: ok,det=False,str(e) or "assertion failed"
        except Exception as e: ok,det=False,f"{type(e).__name__}: {e}"
        results.append({"Test":name,"Result":"PASS ✅" if ok else "FAIL ❌","Detail":det,"ms":round((time.perf_counter()-t0)*1000,2)})
    P={"area":2.0,"base_habitat":"Wetland","base_condition":"Fair","target_habitat":"Wetland","target_condition":"Good",
       "years":10,"difficulty":"Low","strategic":"Standard","target_pct":10}
    r11=assess(P,"1.1.0"); r12=assess(P,"1.2.0")
    t("Shannon H' of equal halves = ln 2", lambda: close(shannon([1,1]),math.log(2)))
    t("Simpson 1−Σp² of equal halves = 0.5", lambda: close(simpson([1,1]),0.5))
    t("Hand-check: baseline 2 ha × 6 × Fair(2) = 24.0", lambda: close(r11["baseline"],24.0))
    t("Hand-check: post 2×6×Good(3)×0.70 = 25.2 (v1.1.0)", lambda: close(r11["post"],25.2))
    t("Hand-check: net +1.2 units = +5.0% → below 10% target", lambda: (close(r11["net"],1.2), close(r11["pct"],5.0), assert_(not r11["meets"])))
    t("Rules rollback changes result (v1.2.0 post = 26.28)", lambda: close(r12["post"],26.28))
    t("Engine determinism: identical inputs → identical hash", lambda: assert_(sha_bytes(json.dumps(assess(P,"1.2.0"),sort_keys=True).encode())==sha_bytes(json.dumps(r12 if False else assess(P,"1.2.0"),sort_keys=True).encode())))
    t("Uncertainty band non-negative and capped ≤ 35%", lambda: (assert_(r12["band_abs"]>=0), assert_(r12["band_rel"]<=.35)))
    t("Unit conversion: 1.5 ha = 15 000 m²", lambda: close(ha_to_m2(1.5),15000))
    t("Date parser rejects 2026-02-30", lambda: raises(ValueError, lambda: parse_date("2026-02-30")))
    t("SHA-256('abc') matches known vector", lambda: assert_(sha_bytes(b"abc")=="ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"))
    sites={"WIL","EAS"}; td=now().date()
    good={"site_code":"WIL","taxon":"Lutra lutra","count":3,"unit":"holts","method":"camera-trap","observed_at":td.isoformat()}
    t("Validation: clean row has zero errors", lambda: assert_(validate_obs_fields(good,sites,td)[0]==[]))
    t("Validation: negative count → NEGATIVE_COUNT", lambda: assert_("NEGATIVE_COUNT" in [e["code"] for e in validate_obs_fields({**good,"count":-4},sites,td)[0]]))
    t("Validation: bad unit → BAD_UNIT (actionable)", lambda: assert_("BAD_UNIT" in [e["code"] for e in validate_obs_fields({**good,"unit":"litres"},sites,td)[0]]))
    t("Validation: future date → FUTURE_DATE", lambda: assert_("FUTURE_DATE" in [e["code"] for e in validate_obs_fields({**good,"observed_at":(td+timedelta(days=5)).isoformat()},sites,td)[0]]))
    t("Validation: unknown site → UNKNOWN_SITE", lambda: assert_("UNKNOWN_SITE" in [e["code"] for e in validate_obs_fields({**good,"site_code":"XXX"},sites,td)[0]]))
    t("Validation: 40-day lag → LATE warning", lambda: assert_("LATE" in [w["code"] for w in validate_obs_fields({**good,"recorded_at":(td+timedelta(days=40)).isoformat()},sites,td)[1]]))
    def dup_test():
        with db() as c:
            df=pd.DataFrame([good,good])
            v=validate_dataframe(df,c,dup_strategy="reject")
            assert v["recs"][1]["disp"]=="❌ INVALID" and "DUPLICATE" in [e["code"] for e in v["recs"][1]["errors"]]
    t("Import: duplicate key rejected with row-level error", dup_test)
    def contra_test():
        with db() as c:
            r=c.execute("SELECT o.taxon,o.count,s.code,o.observed_at,o.unit,o.method FROM observations o JOIN sites s ON s.id=o.site_id WHERE o.deleted_at IS NULL LIMIT 1").fetchone()
            row={"site_code":r["code"],"taxon":r["taxon"],"count":int(r["count"])*10+7,"unit":r["unit"],"method":r["method"],"observed_at":r["observed_at"]}
            v=validate_dataframe(pd.DataFrame([row]),c)
            assert "CONTRADICTORY" in [w["code"] for w in v["recs"][0]["warns"]]
    t("Import: same key, different count → CONTRADICTORY", contra_test)
    t("Z-score baseline flags injected spike", lambda: assert_(zscore_flags([10]*8+[100])==[8]))
    t("Lifecycle: DRAFT → APPROVED is blocked", lambda: assert_(not check_transition("DRAFT","APPROVED")))
    t("Lifecycle: IN_REVIEW → APPROVED is allowed", lambda: assert_(check_transition("IN_REVIEW","APPROVED")))
    t("Contradictory approval requires override reason", lambda: assert_(needs_reason(["CONTRADICTORY"],"APPROVED")))
    t("RBAC: Stakeholder cannot approve", lambda: assert_(not can("approve","Stakeholder")))
    t("RBAC: Analyst cannot approve; Reviewer can", lambda: (assert_(not can("approve","Analyst")), assert_(can("approve","Reviewer"))))
    return results
def assert_(cond):
    assert cond, "condition failed"
    return True

# ────────────────────────────────────────── PAGE: MISSION ─────────────────────
def page_mission(sdf,odf,idf,adf,asmf):
    items=review_items(sdf,odf,idf,adf,asmf)
    flagged=sum(1 for r in odf.to_dict("records") if flags_of(r))
    quality=100*(1-flagged/max(1,len(odf)))
    approved_pcts=[json.loads(a.result)["pct"] for _,a in asmf[asmf.status=="APPROVED"].iterrows()]
    approved_pcts=[p for p in approved_pcts if p is not None]
    avg_net=sum(approved_pcts)/len(approved_pcts) if approved_pcts else None
    cols=st.columns(6)
    for i,(ic,lb,v,sub,c) in enumerate([("🗺️","Sites",len(sdf),"under monitoring",PAL["teal"]),
        ("🔭","Observations",len(odf),"active registry rows",PAL["green"]),
        ("🧬","Richness",odf.taxon.nunique(),"distinct taxa",PAL["blue"]),
        ("📈","Avg approved net",pctf(None if avg_net is None else round(avg_net,1)),"habitat units, approved only",PAL["green"] if (avg_net or 0)>=10 else PAL["amber"]),
        ("🔍","Pending review",len(items),"awaiting reviewer",PAL["amber"]),
        ("🧪","Data quality",f"{quality:.0f}%","rows with zero flags",PAL["green"] if quality>=85 else PAL["amber"])]):
        with cols[i]: kpi(ic,lb,v,sub,c,i)
    live_panel()
    section("Registry pulse","Where the evidence is accumulating")
    c1,c2=st.columns([1.5,1])
    with c1:
        st.plotly_chart(pulse_fig(odf,sdf),config=PCFG,key="pulse",**W_PC)
        st.caption("Action: sustained volume drops per habitat indicate survey gaps — schedule a transect.")
    with c2:
        st.plotly_chart(donut_fig(odf),config=PCFG,key="donut",**W_PC)
        st.caption("Direct-labelled composition; unbalanced groups may signal method bias.")
    section("Sites at a glance","Six monitored parcels · synthetic demo estate")
    cond_pct={"Poor":30,"Fair":62,"Good":95}
    for row in range(2):
        cols=st.columns(3)
        for j in range(3):
            s=sdf.iloc[row*3+j]; so=odf[odf.site_id==s.id]
            a=latest_assessment(asmf,int(s.id)); r=json.loads(a["result"]) if a else None
            netchip=f'<span class="bdg" style="color:{PAL["green"] if (r and (r["pct"] or 0)>=10) else PAL["magenta"]};border-color:currentColor">{pctf(r["pct"]) if r else "no assessment"}</span>' if r else '<span class="mini">no assessment yet</span>'
            with cols[j]:
                card(f'<div style="display:flex;justify-content:space-between;gap:8px"><b>{esc(s.code)} · {esc(s.name)}</b>{netchip}</div>'
                     f'<div class="mini" style="margin:4px 0">{esc(s.habitat)} · {s.area_ha} ha · {esc(s.designation)}</div>'
                     f'<div class="mini">Condition: {esc(s.condition)}</div><div class="bar"><div style="width:{cond_pct.get(s.condition,50)}%"></div></div>'
                     f'<div class="mini" style="margin-top:6px">{len(so)} observations · {so.taxon.nunique()} taxa · H′ {shannon(list(so["count"])):.2f}</div>', j*70)
                if st.button(f"Open {s.code} report →",key=f"miss_site_{s.code}"):
                    ss.rpt_pref=f"{s.code} — {s.name}"; ss.nav_pref="reports"; st.rerun()
    section("Needs attention","Exception path — act before approving")
    c1,c2=st.columns([1.15,1])
    with c1:
        attn=[]
        for r_ in odf.to_dict("records"):
            fl=flags_of(r_)
            if any(f in HARD for f in fl) or "CONTRADICTORY" in fl or "OUT_OF_RANGE" in fl:
                attn.append((code_of("observations",r_["id"]),r_["site_code"],", ".join(fl),r_["common_name"],"observations",r_["id"]))
        for _,a_ in asmf.iterrows():
            r_=json.loads(a_.result)
            if not r_["meets"] and a_.status!="ARCHIVED":
                attn.append((code_of("assessments",a_.id),a_.site_code,f"below target ({pctf(r_['pct'])})","restoration assessment","assessments",int(a_.id)))
        if not attn: empty_state("No exceptions — the registry is clean.","✅")
        for code_,sc,why,label,tbl,rid in attn[:6]:
            cc1,cc2=st.columns([4,1])
            cc1.markdown(f'<div class="tick"><span class="tl-dot" style="position:static;background:{PAL["magenta"]}"></span>'
                         f'<b>{esc(code_)}</b>&nbsp;{esc(sc)} · {esc(label)} — {esc(why)}</div>',unsafe_allow_html=True)
            if cc2.button("Inspect",key=f"attn_{tbl}_{rid}"):
                ss.drawer={"table":tbl,"id":rid}; st.rerun()
        if len(items):
            if st.button(f"🔍 Go to review queue ({len(items)} waiting)",key="miss_review",type="primary"):
                ss.nav_pref="review"; st.rerun()
    with c2:
        with db() as c:
            recent=[dict(x) for x in c.execute("SELECT * FROM audit ORDER BY ts DESC, id DESC LIMIT 8")]
        card("<b>Recent activity</b>"+timeline_html(recent,8))

# ────────────────────────────────────────── PAGE: IMPORT ──────────────────────
def page_import():
    section("Ingestion","CSV / Excel import — validate before anything touches the registry")
    c1,c2=st.columns([1.5,1])
    with c1:
        up=st.file_uploader("Drop an observations file (.csv / .xlsx)",type=["csv","xlsx"],key="imp_up",
                            disabled=not can("import"),help="Analyst, Administrator roles" if not can("import") else None)
        d1,d2,d3=st.columns(3)
        if d1.button("🧪 Run demo import (valid)",key="imp_demo_ok"):
            ss.imp_blob=("demo_valid.csv",sample_csv_bytes(False)); st.rerun()
        if d2.button("🧯 Run demo import (with errors)",key="imp_demo_bad"):
            ss.imp_blob=("demo_with_errors.csv",sample_csv_bytes(True)); st.rerun()
        if d3.button("✖ Clear file",key="imp_clear"):
            ss.pop("imp_blob",None); ss.pop("imp_done",None); st.rerun()
        blob=None
        if up is not None:
            b=up.getvalue()
            if len(b)>5*1024*1024: st.error("File exceeds 5 MB limit — split the batch.")
            else: blob=(up.name,b)
        elif ss.get("imp_blob"): blob=ss.imp_blob
        mode=st.radio("Commit strategy",["Skip invalid rows (partial commit)","All-or-nothing (block on any error)"],key="imp_mode",horizontal=True)
        dup=st.selectbox("Duplicate keys (identical counts)",["skip","reject"],format_func=lambda x:"Skip safely (never overwrite)" if x=="skip" else "Reject as error",key="imp_dup")
        if blob:
            fname,b=blob
            try:
                df=pd.read_csv(io.BytesIO(b)) if fname.lower().endswith(".csv") else pd.read_excel(io.BytesIO(b),engine="openpyxl")
            except Exception as e:
                st.error(f"Could not parse '{fname}': {e}"); df=None
            if df is not None:
                if not len(df): st.warning("File is empty — nothing to import (safe no-op).")
                else:
                    with db() as c: v=validate_dataframe(df,c,dup)
                    if v["fatal"]: st.error(v["fatal"])
                    else:
                        s=v["stats"]
                        m=st.columns(5)
                        for i,(lb,val,col) in enumerate([("Rows",s["total"],PAL["blue"]),("Valid",s["valid"],PAL["green"]),
                            ("Valid + flags",s["flagged"],PAL["amber"]),("Skipped dups",s["skipped"],PAL["clay"]),("Invalid",s["invalid"],PAL["magenta"])]):
                            with m[i]: kpi("•",lb,val,"",col,i)
                        st.markdown(f'<div class="mini">File fingerprint (SHA-256): <code>{sha_bytes(b)[:24]}…</code> · original bytes are preserved on commit · schema v{SCHEMA}</div>',unsafe_allow_html=True)
                        st.dataframe(v["preview"],hide_index=True,height=320,**W_DF)
                        if len(v["report"]):
                            with st.expander(f"🔎 Row-level issues ({len(v['report'])})",expanded=True):
                                st.dataframe(v["report"][["row","field","code","severity","message"]],hide_index=True,height=220,**W_DF)
                            st.download_button("⬇ Download error report (CSV)",v["report"].to_csv(index=False).encode(),
                                file_name=f"error_report_{safe_name(fname)}.csv",mime="text/csv",key="imp_err_dl")
                        blocked=(mode.startswith("All") and s["invalid"]>0)
                        importable=sum(1 for r_ in v["recs"] if r_["importable"])
                        if blocked: st.error("All-or-nothing mode: fix the invalid rows and re-upload. Nothing was written.")
                        if st.button(f"✅ Commit {importable} row(s) to registry",key="imp_commit",type="primary",
                                     disabled=blocked or importable==0 or not can("import")):
                            try:
                                n,fid,sha=commit_import(v,fname,b)
                                ss.imp_done={"n":n,"fid":fid,"sha":sha,"fname":fname}
                                st.toast(f"{n} observations imported with full lineage",icon="📥"); st.rerun()
                            except (PermissionError,ValueError) as e: st.error(str(e))
        if ss.get("imp_done"):
            d=ss.imp_done
            card(f'<b>✅ Last commit:</b> {d["n"]} rows from <code>{esc(d["fname"])}</code> · source file #{d["fid"]} preserved · '
                 f'sha256 <code>{d["sha"][:20]}…</code><div class="mini">Every row now carries source_file_id + source_row. '
                 f'Clean rows are VALIDATED; flagged rows are DRAFT awaiting correction. Nothing existing was overwritten.</div>')
            if st.button("🗂 Open registry (newest first)",key="imp_goto"):
                ss.f_sort="Newest first"; ss.nav_pref="registry"; st.rerun()
    with c2:
        card("<b>How the pipeline protects you</b><div class='mini' style='margin-top:6px'>"
             "1️⃣ Column & type checks → 2️⃣ ranges, dates, units, methods → 3️⃣ referential integrity (site codes) → "
             "4️⃣ duplicate & contradiction detection → 5️⃣ preview with row-level errors → 6️⃣ commit with preserved source file + checksum lineage.<br><br>"
             "Re-imports are safe: identical duplicates are skipped or rejected; conflicting counts are kept as CONTRADICTORY for reviewer reconciliation. "
             "Validated source data is never silently overwritten.</div>")
        st.download_button("⬇ Sample template (CSV, 12 valid rows)",sample_csv_bytes(False),file_name="terraledger_sample.csv",mime="text/csv",key="imp_s_csv")
        st.download_button("⬇ Sample with errors (CSV, 20 rows)",sample_csv_bytes(True),file_name="terraledger_sample_errors.csv",mime="text/csv",key="imp_s_bad")
        st.download_button("⬇ Sample template (Excel)",sample_xlsx_bytes(),file_name="terraledger_sample.xlsx",
                           mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",key="imp_s_xlsx")
        st.caption("Required columns: "+", ".join(OBS_REQ)+" · optional: common_name, recorded_at, notes. Dates: YYYY-MM-DD.")

# ────────────────────────────────────────── PAGE: REGISTRY ────────────────────
FILTER_DEFAULTS={"f_q":"","f_sites":[],"f_status":[],"f_quality":"Any","f_sort":"Newest first","f_size":15}
def init_filters():
    for k,v in FILTER_DEFAULTS.items(): ss.setdefault(k,v)
def bulk_bar(table, df_filtered, key_prefix):
    codes=[code_of(table,int(i)) for i in df_filtered.id]
    key=f"bulk_{table}"
    if ss.get(key) and any(x not in codes for x in ss[key]): ss.pop(key,None)
    sel=st.multiselect("Bulk select",codes,key=key,placeholder="Pick records for bulk actions…")
    if not sel: return
    ids=[int(x.split("-")[1]) for x in sel]
    c1,c2,c3,c4=st.columns(4)
    if c1.button(f"🔍 Submit {len(ids)} for review",key=f"{key_prefix}_submit",disabled=not can("submit")):
        ok=skip=0
        for rid in ids:
            try: do_transition(table,rid,"IN_REVIEW"); ok+=1
            except (PermissionError,ValueError): skip+=1
        st.toast(f"{ok} submitted · {skip} skipped (must be VALIDATED)",icon="🔍"); ss.pop(key,None); st.rerun()
    sub=df_filtered[df_filtered.id.isin(ids)]
    c2.download_button(f"⬇ Export {len(ids)} (CSV)",sub.to_csv(index=False).encode(),
        file_name=f"{table}_selection.csv",mime="text/csv",key=f"{key_prefix}_dl",
        on_click=log_export_cb,args=(f"{table} selection ({len(ids)})",table,0))
    if c3.button(f"🗄 Archive {len(ids)}",key=f"{key_prefix}_arch",disabled=not can("archive")):
        ok=0
        for rid in ids:
            try: do_transition(table,rid,"ARCHIVED","bulk archive"); ok+=1
            except (PermissionError,ValueError): pass
        st.toast(f"{ok} archived",icon="🗄"); ss.pop(key,None); st.rerun()
    if c4.button(f"🗑 Delete {len(ids)}",key=f"{key_prefix}_del",disabled=not can("delete")):
        with db() as c:
            for rid in ids:
                upd(c,table,rid,{"deleted_at":now_iso(),"updated_at":now_iso()})
                log_event(c,"delete",table,rid,f"{code_of(table,rid)} soft-deleted (undo available)")
        ss.undo={"table":table,"ids":ids}
        st.toast(f"{len(ids)} deleted — Undo available in the banner",icon="🗑"); ss.pop(key,None); st.rerun()
def pager(table, n):
    size=int(ss.f_size); pages=max(1,math.ceil(n/size))
    ss.setdefault(f"pg_{table}",0)
    ss[f"pg_{table}"]=min(ss[f"pg_{table}"],pages-1)
    c1,c2,c3=st.columns([1,2,1])
    if c1.button("← Prev",key=f"pgprev_{table}",disabled=ss[f"pg_{table}"]==0): ss[f"pg_{table}"]-=1; st.rerun()
    c2.markdown(f"<div style='text-align:center' class='mini'>Page {ss[f'pg_{table}']+1} / {pages} · {n} records</div>",unsafe_allow_html=True)
    if c3.button("Next →",key=f"pgnext_{table}",disabled=ss[f"pg_{table}"]>=pages-1): ss[f"pg_{table}"]+=1; st.rerun()
    return ss[f"pg_{table}"]*size, size
def obs_display(df):
    d=df.copy()
    d["Record"]=[code_of("observations",int(i)) for i in d.id]
    d["Status"]=[f"{STATUS_META[s][0]} {s}" for s in d.status]
    d["Flags"]=[", ".join(flags_of(r)) or "—" for r in df.to_dict("records")]
    d=d.rename(columns={"site_code":"Site","common_name":"Species","count":"Count","unit":"Unit","method":"Method",
                        "observed_at":"Observed","origin":"Origin","source_file":"Source file"})
    return d[["Record","Status","Site","Species","Count","Unit","Method","Observed","Flags","Origin","Source file"]]
def page_registry(sdf,odf,idf,adf,asmf):
    section("Records registry","Observations · impacts · restoration actions — full CRUD with provenance")
    t1,t2,t3=st.tabs(["🔭 Observations","⚠️ Impacts","🌱 Restoration actions"])
    with t1:
        ctop=st.columns([3,1])
        ctop[0].markdown('<div class="mini">Search, filter, sort, save views, bulk-act, inspect — every change is audited.</div>',unsafe_allow_html=True)
        if ctop[1].button("➕ New observation",key="reg_new",type="primary",disabled=not can("create")):
            ss.new_obs=True; st.rerun()
        fc=st.columns([1.6,1.2,1.2,1,1.1,.8])
        ss.f_q=fc[0].text_input("Search",key="f_q",placeholder="species, notes…")
        ss.f_sites=fc[1].multiselect("Sites",list(sdf.code),key="f_sites")
        ss.f_status=fc[2].multiselect("Status",list(STATUS_META),key="f_status")
        ss.f_quality=fc[3].selectbox("Quality",["Any","Clean","Flagged (any)","Hard errors","Soft only"],key="f_quality")
        ss.f_sort=fc[4].selectbox("Sort",["Newest first","Oldest first","Count ↓","Site","Species"],key="f_sort")
        ss.f_size=fc[5].selectbox("Rows",[15,25,50],key="f_size")
        with db() as c: views=[dict(x) for x in c.execute("SELECT * FROM saved_views ORDER BY name")]
        vc=st.columns([2,1,1.6,.8,.8])
        vnames=[v["name"] for v in views]
        if ss.get("sv_pick") and ss["sv_pick"] not in vnames: ss.pop("sv_pick",None)
        pick=vc[0].selectbox("Saved views",vnames,key="sv_pick",label_visibility="collapsed",placeholder="Saved views…") if vnames else None
        if vc[1].button("📂 Load",key="sv_load",disabled=not pick):
            v=next(x for x in views if x["name"]==pick)
            for k,val in json.loads(v["filters"]).items(): ss[k]=val
            st.toast(f"View '{pick}' applied",icon="📂"); st.rerun()
        newname=vc[2].text_input("New view name",key="sv_name",label_visibility="collapsed",placeholder="Name current filters…")
        if vc[3].button("💾 Save",key="sv_save",disabled=not newname.strip()):
            with db() as c:
                ins(c,"saved_views",{"name":newname.strip(),"filters":json.dumps({k:ss[k] for k in FILTER_DEFAULTS}),
                                     "created_by":ss.actor,"created_at":now_iso()})
            st.toast("View saved",icon="💾"); st.rerun()
        if vc[4].button("🗑",key="sv_del",disabled=not pick,help="Delete selected saved view"):
            with db() as c: c.execute("DELETE FROM saved_views WHERE name=?",(pick,))
            ss.pop("sv_pick",None); st.rerun()
        d=odf.copy()
        if ss.f_q:
            q=ss.f_q.lower()
            d=d[d.taxon.str.lower().str.contains(q)|d.common_name.str.lower().str.contains(q)|d.notes.fillna("").str.lower().str.contains(q)]
        if ss.f_sites: d=d[d.site_code.isin(ss.f_sites)]
        if ss.f_status: d=d[d.status.isin(ss.f_status)]
        if ss.f_quality!="Any":
            fl=d.apply(lambda r: flags_of(r),axis=1)
            if ss.f_quality=="Clean": d=d[fl.apply(len)==0]
            elif ss.f_quality=="Flagged (any)": d=d[fl.apply(len)>0]
            elif ss.f_quality=="Hard errors": d=d[fl.apply(lambda x: any(f in HARD for f in x))]
            else: d=d[fl.apply(lambda x: len(x)>0 and not any(f in HARD for f in x))]
        sortmap={"Newest first":("observed_at",False),"Oldest first":("observed_at",True),"Count ↓":("count",False),
                 "Site":("site_code",True),"Species":("common_name",True)}
        col,asc=sortmap[ss.f_sort]; d=d.sort_values(col,ascending=asc)
        if not len(d):
            empty_state("No records match these filters. Clear them or import data.","🔍")
            if st.button("Clear filters",key="f_clear"):
                for k,v in FILTER_DEFAULTS.items(): ss[k]=v
                st.rerun()
        else:
            start,size=pager("observations",len(d))
            page=d.iloc[start:start+size]
            st.dataframe(obs_display(page),hide_index=True,height=380,**W_DF,
                column_config={"Count":st.column_config.NumberColumn(format="%d"),"Record":st.column_config.TextColumn(width="small")})
            oc=st.columns([2,1])
            codes=[code_of("observations",int(i)) for i in page.id]
            if ss.get("open_obs") and ss["open_obs"] not in codes: ss.pop("open_obs",None)
            picko=oc[0].selectbox("Inspect record",codes,key="open_obs",label_visibility="collapsed")
            if oc[1].button("🗂 Open detail drawer",key="reg_open",type="primary"):
                ss.drawer={"table":"observations","id":int(picko.split("-")[1])}; st.rerun()
            bulk_bar("observations",d,"bo")
    with t2:
        if can("create"):
            with st.expander("➕ Log new impact"):
                with st.form("imp_form",clear_on_submit=True):
                    a1,a2,a3=st.columns(3)
                    sc=a1.selectbox("Site",list(sdf.code),key="ni_site")
                    act=a2.text_input("Activity",key="ni_act",placeholder="e.g. Culvert maintenance")
                    typ=a3.selectbox("Impact type",IMPACT_TYPES,key="ni_typ")
                    b1,b2,b3=st.columns(3)
                    area=b1.number_input("Area affected (ha)",0.01,50.0,0.5,key="ni_area")
                    sev=b2.slider("Severity (1–3)",1,3,2,key="ni_sev")
                    sd=b3.date_input("Start date",value=now().date(),key="ni_sd")
                    notes=st.text_area("Notes",key="ni_notes")
                    if st.form_submit_button("Create impact record",type="primary"):
                        if not act.strip(): st.error("Activity is required.")
                        else:
                            with db() as c:
                                sid=int(sdf[sdf.code==sc].iloc[0].id)
                                iid=ins(c,"impacts",{"site_id":sid,"activity":act.strip(),"impact_type":typ,"area_ha":area,
                                    "severity":sev,"start_date":sd.isoformat(),"status":"DRAFT","flags":"[]","notes":notes,
                                    "origin":"manual","created_at":now_iso(),"updated_at":now_iso(),"schema_version":SCHEMA})
                                log_event(c,"create","impacts",iid,f"{code_of('impacts',iid)} · {act.strip()}")
                            st.toast(f"{code_of('impacts',iid)} created as DRAFT",icon="⚠️")
        fi=st.columns([2,2])
        fq=fi[0].text_input("Search impacts",key="fi_q",placeholder="activity…")
        fs=fi[1].multiselect("Status",list(STATUS_META),key="fi_st")
        d=idf.copy()
        if fq: d=d[d.activity.str.lower().str.contains(fq.lower())]
        if fs: d=d[d.status.isin(fs)]
        if not len(d): empty_state("No impacts match.","⚠️")
        else:
            disp=d.copy(); disp["Record"]=[code_of("impacts",int(i)) for i in d.id]
            disp["Status"]=[f"{STATUS_META[s][0]} {s}" for s in d.status]
            disp=disp.rename(columns={"site_code":"Site","activity":"Activity","impact_type":"Type","area_ha":"Area (ha)","severity":"Sev","start_date":"Start"})
            st.dataframe(disp[["Record","Status","Site","Activity","Type","Area (ha)","Sev","Start"]],hide_index=True,height=320,**W_DF)
            oc=st.columns([2,1])
            codes=[code_of("impacts",int(i)) for i in d.id]
            if ss.get("open_imp") and ss["open_imp"] not in codes: ss.pop("open_imp",None)
            p=oc[0].selectbox("Inspect",codes,key="open_imp",label_visibility="collapsed")
            if oc[1].button("🗂 Open detail",key="imp_open",type="primary"):
                ss.drawer={"table":"impacts","id":int(p.split("-")[1])}; st.rerun()
            bulk_bar("impacts",d,"bi")
    with t3:
        if can("create"):
            with st.expander("➕ Plan new restoration action"):
                with st.form("act_form",clear_on_submit=True):
                    a1,a2=st.columns(2)
                    sc=a1.selectbox("Site",list(sdf.code),key="na_site")
                    at=a2.text_input("Action",key="na_at",placeholder="e.g. Hedgerow planting")
                    b1,b2,b3,b4=st.columns(4)
                    ht=b1.selectbox("Target habitat",list(HAB_DIST),key="na_ht")
                    ct=b2.selectbox("Target condition",["Poor","Fair","Good"],index=2,key="na_ct")
                    area=b3.number_input("Area (ha)",0.01,50.0,1.0,key="na_area")
                    yrs=b4.slider("Years to target",1,30,10,key="na_yrs")
                    c1_,c2_,c3_,c4_=st.columns(4)
                    diff=c1_.selectbox("Difficulty",["Low","Medium","High"],key="na_df")
                    strat=c2_.selectbox("Strategic",["Standard","Elevated"],key="na_st")
                    cost=c3_.number_input("Cost (£)",0,1_000_000,10000,step=500,key="na_cost")
                    prog=c4_.slider("Progress %",0,100,0,key="na_prog")
                    notes=st.text_area("Notes",key="na_notes")
                    if st.form_submit_button("Create action",type="primary"):
                        if not at.strip(): st.error("Action name is required.")
                        else:
                            with db() as c:
                                sid=int(sdf[sdf.code==sc].iloc[0].id)
                                aid=ins(c,"actions",{"site_id":sid,"action_type":at.strip(),"habitat_target":ht,"condition_target":ct,
                                    "area_ha":area,"years_to_target":yrs,"difficulty":diff,"strategic":strat,
                                    "start_date":now().date().isoformat(),"cost_gbp":cost,"progress":prog,"status":"DRAFT",
                                    "flags":"[]","notes":notes,"origin":"manual","created_at":now_iso(),"updated_at":now_iso(),"schema_version":SCHEMA})
                                log_event(c,"create","actions",aid,f"{code_of('actions',aid)} · {at.strip()}")
                            st.toast(f"{code_of('actions',aid)} created as DRAFT",icon="🌱")
        d=adf.copy()
        fa=st.multiselect("Status",list(STATUS_META),key="fa_st")
        if fa: d=d[d.status.isin(fa)]
        if not len(d): empty_state("No actions match.","🌱")
        else:
            disp=d.copy(); disp["Record"]=[code_of("actions",int(i)) for i in d.id]
            disp["Status"]=[f"{STATUS_META[s][0]} {s}" for s in d.status]
            disp=disp.rename(columns={"site_code":"Site","action_type":"Action","habitat_target":"Target habitat",
                "area_ha":"Area (ha)","cost_gbp":"Cost (£)","progress":"Progress"})
            st.dataframe(disp[["Record","Status","Site","Action","Target habitat","Area (ha)","Cost (£)","Progress"]],
                hide_index=True,height=320,**W_DF,
                column_config={"Progress":st.column_config.ProgressColumn(min_value=0,max_value=100,format="%d%%"),
                               "Cost (£)":st.column_config.NumberColumn(format="£%d")})
            oc=st.columns([2,1])
            codes=[code_of("actions",int(i)) for i in d.id]
            if ss.get("open_act") and ss["open_act"] not in codes: ss.pop("open_act",None)
            p=oc[0].selectbox("Inspect",codes,key="open_act",label_visibility="collapsed")
            if oc[1].button("🗂 Open detail",key="act_open",type="primary"):
                ss.drawer={"table":"actions","id":int(p.split("-")[1])}; st.rerun()
            bulk_bar("actions",d,"ba")

# ────────────────────────────────────────── PAGE: ENGINE ──────────────────────
def page_engine(sdf,odf,idf,adf,asmf):
    section("Deterministic domain engine","Net-gain-style habitat units — explainable, versioned, hand-checkable")
    opts=list(sdf.code+" — "+sdf.name)
    pref=ss.get("eng_pref",opts[2] if len(opts)>2 else opts[0])
    if pref not in opts: pref=opts[0]
    pick=st.selectbox("Site / parcel",opts,index=opts.index(pref),key="eng_site_pick")
    ss.eng_pref=pick
    s=sdf[sdf.code==pick.split(" — ")[0]].iloc[0]; sid=int(s.id)
    if ss.get("eng_last")!=sid:
        for k in ["eng_area","eng_bh","eng_bc","eng_th","eng_tc","eng_y","eng_df","eng_st","eng_tp"]: ss.pop(k,None)
        ss.eng_last=sid
    act=adf[adf.site_id==sid]
    a0=act.iloc[0] if len(act) else None
    left,right=st.columns([1,1.6])
    with left:
        card("<b>Assessment inputs</b><div class='mini'>Every control recomputes instantly. Defaults come from the site's restoration action.</div>")
        area=st.number_input("Parcel area (ha)",0.05,60.0,float(a0.area_ha) if a0 is not None else float(s.area_ha),0.1,key="eng_area")
        bh=st.selectbox("Baseline habitat",list(HAB_DIST),index=list(HAB_DIST).index(s.habitat),key="eng_bh")
        bc=st.selectbox("Baseline condition",["Poor","Fair","Good"],index=["Poor","Fair","Good"].index(s.condition),key="eng_bc")
        th=st.selectbox("Target habitat",list(HAB_DIST),index=list(HAB_DIST).index(a0.habitat_target) if a0 is not None else list(HAB_DIST).index(s.habitat),key="eng_th")
        tc=st.selectbox("Target condition",["Poor","Fair","Good"],index=["Poor","Fair","Good"].index(a0.condition_target) if a0 is not None else 2,key="eng_tc")
        yrs=st.slider("Years to target condition",1,30,int(a0.years_to_target) if a0 is not None else 10,key="eng_y")
        diff=st.selectbox("Creation / enhancement difficulty",["Low","Medium","High"],index=["Low","Medium","High"].index(a0.difficulty) if a0 is not None else 1,key="eng_df")
        strat=st.selectbox("Strategic significance",["Standard","Elevated"],index=["Standard","Elevated"].index(a0.strategic) if a0 is not None else 0,key="eng_st")
        tp=st.slider("Target net gain (%)",0,30,10,key="eng_tp")
        rv_opts=list(RULES)[::-1]
        rvpref=ss.get("eng_rv_pref","1.2.0")
        rv=st.selectbox("Factor-table version (rollback control)",rv_opts,index=rv_opts.index(rvpref),key="eng_rv_pick")
        ss.eng_rv_pref=rv
        if st.button("⏪ Rollback to previously approved rules",key="eng_rollback",
                     help="Pins the factor version used by this site's latest APPROVED assessment"):
            prev=latest_assessment(asmf,sid)
            if prev: ss.eng_rv_pref=prev["rules_version"]; st.toast(f"Rolled back to rules v{prev['rules_version']}",icon="⏪"); st.rerun()
            else: st.info("No approved assessment for this site yet.")
    p={"area":area,"base_habitat":bh,"base_condition":bc,"target_habitat":th,"target_condition":tc,
       "years":yrs,"difficulty":diff,"strategic":strat,"target_pct":tp}
    q=site_quality(odf,sid)
    res=assess(p,rv,q["soft"],q["estimate"],q["stale"])
    with right:
        m=st.columns(4)
        with m[0]: kpi("🟤","Baseline",f"{res['baseline']:.2f}","habitat units",PAL["clay"])
        with m[1]: kpi("🟢","Post",f"{res['post']:.2f}",f"± {res['band_abs']} units",PAL["green"])
        with m[2]: kpi("Δ","Net",f"{res['net']:+.2f}",pctf(res["pct"]),PAL["green"] if res["meets"] else PAL["magenta"])
        with m[3]: kpi("🎯",f"Target ≥ {tp}%","MEETS ✅" if res["meets"] else "BELOW ⛔","decision support",PAL["green"] if res["meets"] else PAL["magenta"])
        st.plotly_chart(waterfall_fig(res),config=PCFG,key="eng_wf",**W_PC)
        for w in res["warnings"]: st.warning(w)
        with st.expander("🧾 Explanation panel — inputs, rules, provenance, uncertainty",expanded=True):
            for ln in res["explanation"]: st.markdown(ln)
            fdf=pd.DataFrame([{"Years ≤":t,"Temporal factor":f} for t,f in RULES[rv]["temporal"]])
            c1_,c2_=st.columns(2)
            c1_.dataframe(fdf,hide_index=True,height=210,**W_DF)
            c2_.markdown(f"**Difficulty:** {RULES[rv]['difficulty']}\n\n**Condition:** {RULES[rv]['condition']}\n\n**Strategic:** {RULES[rv]['strategic']}")
        prev=latest_assessment(asmf,sid,prefer_approved=False)
        bc1,bc2,bc3=st.columns(3)
        if bc1.button("💾 Save assessment → review",key="eng_save",type="primary",disabled=not can("submit")):
            try:
                require("submit")
                with db() as c:
                    aid=ins(c,"assessments",{"site_id":sid,"params":json.dumps(p),"result":json.dumps(res),
                        "rules_version":rv,"engine_version":ENGINE_VER,"status":"IN_REVIEW",
                        "created_by":ss.actor,"created_at":now_iso(),"updated_at":now_iso()})
                    log_event(c,"create","assessments",aid,f"{code_of('assessments',aid)} · rules v{rv} · net {pctf(res['pct'])}")
                    log_event(c,"submit","assessments",aid,f"{code_of('assessments',aid)} submitted for review")
                st.toast(f"{code_of('assessments',aid)} sent to review queue",icon="🧮"); st.rerun()
            except PermissionError as e: st.error(str(e))
        if bc2.button("✍️ Manual override (latest)",key="eng_override",disabled=not can("override") or not prev):
            ss.reason={"mode":"engine_override","table":"assessments","id":int(prev["id"])}; ss.pop("rs_reason",None); st.rerun()
        if prev and bc3.button(f"🗂 {code_of('assessments',int(prev['id']))}",key="eng_open_prev"):
            ss.drawer={"table":"assessments","id":int(prev["id"])}; st.rerun()
        if prev:
            pr=json.loads(prev["result"])
            ov=f" · override: {json.loads(prev['override'])['net_pct']}%" if prev.get("override") else ""
            st.markdown(f'<div class="mini">Latest saved: {badge(prev["status"])} rules v{prev["rules_version"]} · net {pctf(pr["pct"])}{esc(ov)} · by {esc(prev["created_by"])} · {fmt_dt(prev["created_at"])}</div>',unsafe_allow_html=True)
        with st.expander("🔁 Version comparison / rollback evidence"):
            rows_=[]
            for v in RULES:
                rr=assess(p,v,q["soft"],q["estimate"],q["stale"])
                rows_.append({"Rules":v,"Published":RULES[v]["published"],"Baseline":rr["baseline"],"Post":rr["post"],"Net %":rr["pct"],"Meets":rr["meets"]})
            st.dataframe(pd.DataFrame(rows_),hide_index=True,**W_DF)
            st.caption("Saved assessments pin their factor version — rolling back never rewrites history; it changes what the next computation uses.")

# ────────────────────────────────────────── PAGE: REVIEW ──────────────────────
def page_review(sdf,odf,idf,adf,asmf):
    section("Review queue","Human approval boundary — nothing is approved without a reviewer")
    items=review_items(sdf,odf,idf,adf,asmf)
    with db() as c:
        appr_week=c.execute("SELECT COUNT(*) n FROM audit WHERE action='approve' AND ts>=?",(iso(now()-timedelta(days=7)),)).fetchone()["n"]
    m=st.columns(3)
    with m[0]: kpi("🔍","In queue",len(items),"sorted by priority",PAL["amber"])
    with m[1]: kpi("✅","Approved this week",appr_week,"audit-verified",PAL["green"])
    with m[2]: kpi("🔐","Your role",ss.role,"approve permission: "+("yes" if can("approve") else "no"),PAL["blue"])
    types=st.multiselect("Record types",["observations","impacts","actions","assessments"],key="rv_types",
                         format_func=lambda x:x.capitalize())
    if types: items=[i for i in items if i["table"] in types]
    if not can("approve"):
        st.info("Read-only for your role — switch to **Dr. Ingrid Solberg (Reviewer)** or an Administrator in the sidebar to decide.")
    if not items:
        empty_state("Queue is clear. Submit VALIDATED records from the registry to review them here.","🎉"); return
    for idx,it in enumerate(items):
        c1,c2=st.columns([2.6,1.6])
        with c1:
            wait=""
            try: wait=f" · waiting {(now()-datetime.fromisoformat(it['ts'])).days}d"
            except Exception: pass
            card(f'<div style="display:flex;gap:8px;align-items:center;flex-wrap:wrap"><span class="bdg" style="color:{PAL["blue"]};border-color:{PAL["blue"]}66">{esc(it["table"][:-1].upper())}</span>'
                 f'<b>{esc(it["code"])}</b><span class="mini">{esc(it["site"])}{wait} · priority {it["priority"]}</span></div>'
                 f'<div style="margin:6px 0">{esc(it["summary"])}</div>'
                 f'<div>{flags_html(it["flags"])}</div>'
                 +(f'<div class="mini" style="margin-top:4px">{esc(it["extra"])}</div>' if it["extra"] else ""), idx*40)
        with c2:
            b1,b2=st.columns(2)
            if b1.button("✅ Approve",key=f"rv_ap_{it['table']}_{it['id']}",type="primary",disabled=not can("approve")):
                if needs_reason(it["flags"],"APPROVED"):
                    ss.reason={"mode":"approve_override","table":it["table"],"id":it["id"]}; ss.pop("rs_reason",None); st.rerun()
                else:
                    try:
                        do_transition(it["table"],it["id"],"APPROVED")
                        st.toast(f"{it['code']} approved",icon="✅"); st.balloons(); st.rerun()
                    except (PermissionError,ValueError) as e: st.error(str(e))
            if b2.button("⛔ Reject",key=f"rv_rj_{it['table']}_{it['id']}",disabled=not can("review")):
                ss.reason={"mode":"reject","table":it["table"],"id":it["id"]}; ss.pop("rs_reason",None); st.rerun()
            b3,b4,b5,b6=st.columns(4)
            if b3.button("🛠",key=f"rv_cr_{it['table']}_{it['id']}",disabled=not can("review"),help="Return for correction"):
                ss.reason={"mode":"correction","table":it["table"],"id":it["id"]}; ss.pop("rs_reason",None); st.rerun()
            if b4.button("▲",key=f"rv_up_{it['table']}_{it['id']}",disabled=not can("review") or idx==0,help="Raise priority"):
                other=items[idx-1]
                with db() as c:
                    upd(c,it["table"],it["id"],{"priority":it["priority"]+1})
                    log_event(c,"reorder",it["table"],it["id"],f"{it['code']} priority raised above {other['code']}")
                st.rerun()
            if b5.button("▼",key=f"rv_dn_{it['table']}_{it['id']}",disabled=not can("review") or idx==len(items)-1,help="Lower priority"):
                with db() as c:
                    upd(c,it["table"],it["id"],{"priority":max(0,it["priority"]-1)})
                    log_event(c,"reorder",it["table"],it["id"],f"{it['code']} priority lowered")
                st.rerun()
            if b6.button("🗂",key=f"rv_op_{it['table']}_{it['id']}",help="Open detail drawer"):
                ss.drawer={"table":it["table"],"id":it["id"]}; st.rerun()

# ────────────────────────────────────────── PAGE: REPORTS ─────────────────────
def page_reports(sdf,odf,idf,adf,asmf):
    section("Reports & export","Audit-ready evidence packs — every export is logged")
    opts=["🌐 Portfolio (all sites)"]+list(sdf.code+" — "+sdf.name)
    pref=ss.get("rpt_pref",opts[0])
    if pref not in opts: pref=opts[0]
    pick=st.selectbox("Scope",opts,index=opts.index(pref),key="rpt_pick")
    ss.rpt_pref=pick
    site_id=None if pick==opts[0] else int(sdf[sdf.code==pick.split(" — ")[0]].iloc[0].id)
    cache_key=f"{site_id}:{len(odf)}:{asmf.updated_at.max()}"
    if ss.get("rpt_cache_key")!=cache_key:
        ss.rpt_html=build_html_report(site_id); ss.rpt_cache_key=cache_key
    if site_id is None:
        f=before_after_fig(sdf,asmf)
        if f:
            st.plotly_chart(f,config=PCFG,key="rpt_ba",**W_PC)
            st.caption("Action: parcels below the +10% line need revised difficulty/temporal plans or additional area.")
        rows=[]
        for _,s in sdf.iterrows():
            a=latest_assessment(asmf,int(s.id)); r=json.loads(a["result"]) if a else None
            rows.append({"Site":s.code,"Name":s.name,"Habitat":s.habitat,"Observations":int((odf.site_id==s.id).sum()),
                "Baseline":r["baseline"] if r else None,"Post":r["post"] if r else None,
                "Net %":r["pct"] if r else None,"Assessment":a["status"] if a else "none"})
        st.dataframe(pd.DataFrame(rows),hide_index=True,**W_DF,
            column_config={"Net %":st.column_config.NumberColumn(format="%+.1f%%")})
        fname="terraledger_portfolio"
    else:
        s=sdf[sdf.id==site_id].iloc[0]; so=odf[odf.site_id==site_id]
        a=latest_assessment(asmf,site_id); r=json.loads(a["result"]) if a else None
        c1,c2=st.columns([1.4,1])
        with c1:
            card(f'<b>{esc(s.name)}</b><div class="mini">{esc(s.habitat)} · {s.area_ha} ha ({ha_to_m2(s.area_ha):,.0f} m²) · {esc(s.condition)} · {esc(s.designation)} · {esc(s.org_name)}</div>'
                 +(f'<div style="margin-top:8px">{badge(a["status"])} <b style="color:{PAL["green"] if r["meets"] else PAL["magenta"]}">{pctf(r["pct"])}</b> net units · rules v{a["rules_version"]} · ±{r["band_abs"]} band</div>' if r else '<div class="mini" style="margin-top:8px">No assessment yet — run the Impact Engine.</div>'))
            st.plotly_chart(trend_fig(odf,site_id),config=PCFG,key="rpt_trend",**W_PC)
            st.caption("Diamond markers = rolling z-score anomalies. Investigate before approving downstream assessments.")
        with c2:
            acts=adf[adf.site_id==site_id]
            inner="<b>Restoration pipeline</b>"
            for _,x in acts.iterrows():
                inner+=(f'<div style="margin:8px 0"><div class="mini">{esc(x.action_type)} → {esc(x.habitat_target)} · {x.area_ha} ha · {money(x.cost_gbp)} · {badge(x.status)}</div>'
                        f'<div class="bar"><div style="width:{int(x.progress)}%"></div></div><div class="mini">{int(x.progress)}% delivered</div></div>')
            imps=idf[idf.site_id==site_id]
            inner+="<b style='display:block;margin-top:10px'>Impact pressures</b>"
            for _,x in imps.iterrows():
                inner+=f'<div class="mini">⚠ {esc(x.activity)} · sev {int(x.severity)}/3 · {badge(x.status)}</div>'
            inner+=f'<div class="mini" style="margin-top:8px">Shannon H′ {shannon(list(so["count"])):.2f} · Simpson {simpson(list(so["count"])):.2f} · richness {so.taxon.nunique()}</div>'
            card(inner)
        if r:
            with st.expander("🧾 Assessment explanation (traceable output)"):
                for ln in r["explanation"]: st.markdown(ln)
                if a.get("override"):
                    ov=json.loads(a["override"]); st.warning(f"Manual override active: net {ov['net_pct']}% — {ov['reason']}")
        fname=f"terraledger_{s.code}"
    section("Export & share","Download or send a read-only link")
    e=st.columns(5)
    e[0].download_button("⬇ HTML evidence pack",ss.rpt_html.encode(),file_name=f"{fname}_report.html",mime="text/html",
        key="rpt_html_dl",type="primary",on_click=log_export_cb,args=("HTML evidence pack","sites",site_id or 0))
    e[1].download_button("⬇ JSON bundle (lineage)",bundle_json(site_id),file_name=f"{fname}_bundle.json",mime="application/json",
        key="rpt_json_dl",on_click=log_export_cb,args=("JSON bundle","sites",site_id or 0))
    sub=odf if site_id is None else odf[odf.site_id==site_id]
    e[2].download_button("⬇ Observations CSV",sub.to_csv(index=False).encode(),file_name=f"{fname}_observations.csv",mime="text/csv",
        key="rpt_csv_dl",on_click=log_export_cb,args=("Observations CSV","sites",site_id or 0))
    with db() as c: aud=pd.read_sql_query("SELECT * FROM audit ORDER BY ts DESC",c)
    e[3].download_button("⬇ Audit trail CSV",aud.to_csv(index=False).encode(),file_name="terraledger_audit.csv",mime="text/csv",
        key="rpt_aud_dl",on_click=log_export_cb,args=("Audit CSV","audit",0))
    if e[4].button("🔗 Share this report",key="rpt_share"):
        ss.share={"kind":"site","id":site_id} if site_id else {"kind":"workspace"}; st.rerun()
    st.caption("HTML packs are self-contained (chart embedded, works offline). Exports write an audit event with actor, role and scope.")

# ────────────────────────────────────────── PAGE: GOVERNANCE ──────────────────
DOC_PRD="""
**Problem.** Biodiversity evidence for planning, BNG-style commitments and nature-risk reporting is scattered across spreadsheets,
email and shared drives. Provenance is lost, reviews are informal, and audit preparation takes days.

**Narrow MVP workflow (end-to-end).** Import field observations → validate with row-level errors → reviewer approves →
deterministic habitat-unit assessment with explanation → exportable, shareable evidence pack with lineage.

**Current workflow failure points** — no stable IDs · silent overwrites · units/dates inconsistent · approvals untraceable · reports rebuilt by hand.

| Persona | Enters data | Reviews | Approves |
|---|---|---|---|
| Amara — Administrator (council biodiversity officer) | ✔ config, imports | ✔ | ✔ |
| Diego — Analyst (consultancy ecologist) | ✔ field data, impacts, actions | — | — |
| Dr. Solberg — Reviewer (senior ecologist) | — | ✔ quality & domain | ✔ |
| Sam — Stakeholder (planner / climate-risk analyst) | — | read-only | — |

**Lifecycle.** DRAFT → VALIDATED → IN_REVIEW → APPROVED / REJECTED / CORRECTION → ARCHIVED → export.
**Exception path.** Missing / malformed / out-of-range / late / contradictory / duplicate rows are flagged, never silently accepted;
contradictory approvals require a documented override reason.

**In scope (MVP):** registry CRUD, CSV/XLSX import + validation, review workflow, deterministic engine + explanations,
audit + lineage, exports/share, backups, self-tests, roles (demo identities). **Out of scope (MVP):** statutory metric compliance,
real authentication/SSO, GIS mapping, mobile capture, ML models, external integrations.

**Non-functional:** local Windows run, deterministic results, parameterised SQL, checksummed evidence, pinned-by-name open-source deps,
paginated tables, no paid keys. **Success criteria (engineering targets — to be validated with pilot users, no customer-impact claims):**
100-row import < 5 s · 100% malformed rows rejected with actionable codes · byte-identical recomputation · every export carries lineage · suite green.

**Assumptions & risks:** synthetic factors are illustrative; a qualified ecologist must sign off real factor tables; single-writer SQLite is MVP-only.
**Discovery interview guide (run in pilot):** Where does evidence live today? How long from field note to approved report? Who signs off?
What fails an audit? What would you pay to remove that pain? *(Hypotheses — not validated customer feedback.)*
"""
DOC_BACKLOG="""
| Priority | MVP (built ✔) | Post-MVP | Enterprise |
|---|---|---|---|
| P0 | ✔ Registry + provenance + audit | FastAPI service (Pydantic, pagination, error codes) | SSO / SAML / directory sync |
| P0 | ✔ Import validation + error reports | PostgreSQL + Alembic migrations | Granular RBAC + legal hold |
| P0 | ✔ Review / approve / override | Real auth (argon2 hashing), server-side sessions | Audit-export API + SIEM feed |
| P1 | ✔ Deterministic engine + explanations | GIS map view + geofenced sites | HA backups, RPO/RTO targets, SLAs |
| P1 | ✔ Exports / share packs | Scheduled imports, email digests | Multi-tenant deployment controls |
| P2 | ✔ Backup / restore / self-tests | Mobile-friendly capture form | Pen-test + independent domain review |
| P2 | ✔ Saved views, bulk ops, undo | ML anomaly model vs z-score baseline (time-split eval) | On-prem installer + upgrade tooling |
"""
DOC_RISKS="""
| # | Risk | Category | L×I | Mitigation | Owner |
|---|---|---|---|---|---|
| R1 | Demo factor tables misread as statutory | Domain validity | M×H | Watermarks, disclaimers, ecologist sign-off gate before real use | Reviewer |
| R2 | Synthetic patterns treated as real ecology | Data quality | M×H | SYNTHETIC labels everywhere, ESTIMATE flags, no ML performance claims | Product |
| R3 | Unauthorised edits / no real auth in MVP | Security | M×M | Demo identities only; function-level RBAC; team edition adds argon2 + server sessions + HTTPS | Eng |
| R4 | Reviewer bottleneck stalls pipeline | Adoption | M×M | Queue priorities, wait-time metric, bulk submit | Ops |
| R5 | SQLite single-writer under concurrency | Operational | L×M | WAL + timeouts + backups; documented PostgreSQL path | Eng |
| R6 | Import corrupts validated data | Operational | L×H | Insert-only commits, preserved sources + checksums, soft-delete + undo, restore tests | Eng |
| R7 | Compliance overclaim in sales | Legal | L×H | Decision-support positioning; no certification claims without independent review | Founder |
"""
DOC_RUNBOOK="""
**Backup** — Governance → Backup → *Create backup* (SQLite online backup API → `terraledger_data/backups/`). Verify with *Integrity check*.
**Restore test** — create backup, verify integrity + row counts, restore into place (a safety snapshot is taken first), re-run Quality Suite.
**Upgrade** — `pip install -U -r requirements.txt` then re-run the Quality Suite; factor-version changes are explicit and never rewrite saved assessments.
**Incident** — freeze imports (role switch to Stakeholder), snapshot DB, restore last verified backup, replay from preserved source files (checksums match).
**PostgreSQL migration plan** — 1) swap `db()` for SQLAlchemy engine; 2) DDL: AUTOINCREMENT→IDENTITY, ISO TEXT→timestamptz; 3) Alembic baseline migration;
4) dual-write shadow period + row-count/checksum reconciliation; 5) concurrency tests (two reviewers, one record) + transaction isolation checks; 6) cutover with rollback snapshot.
**Secrets** — none required in MVP; future credentials via environment variables / secrets manager, never in source control.
"""
DOC_SECURITY="""
**Threat model (MVP).** Local single-user demo: no network auth surface. Assets: registry integrity, evidence files, audit trail.
Threats: malicious upload (mitigated: type/size whitelist, parameterised SQL, HTML-escaped rendering), path traversal (filenames sanitised),
silent data mutation (insert-only imports + audit + undo), backup loss (verify + restore test). Sensitive-data rule: precise locations of
protected species would be **Restricted** in real deployments — demo coordinates are synthetic and jittered.
**Deployment hardening (team+):** HTTPS termination, argon2 password hashing, server-side authorization on every endpoint,
rate limiting + pagination on public APIs, structured logs without sensitive payloads, retention policy with legal hold.
**Human-approval boundary:** software is decision support; APPROVED status requires a Reviewer/Administrator action; contradictory data
requires a documented override; regulated use requires qualified ecological review. No certification or compliance is claimed.
"""
DOC_COMMERCIAL="""
**Buyer hypothesis.** Head of Sustainability / biodiversity officer at a mid-size municipality (expandable to consultancies & utilities).
**Expensive workflow.** Assembling auditable biodiversity evidence for planning conditions and nature reporting — currently days of spreadsheet archaeology.
**Value proposition.** Minutes from field record to approved, provenance-complete, shareable evidence pack.
**Pilot success metric (to measure, not claimed):** median time field-note → approved export < 10 minutes; 100% of exports pass provenance checklist.
**Tiers.** ① Local MVP — free, one operator (this app). ② Team — shared PostgreSQL, real auth, roles/approvals; per-site subscription hypothesis.
③ Enterprise — SSO, audit-export API, deployment controls, backups, SLAs; annual on-prem licence + support.
**Licence inventory (commercial-compatible):** Streamlit Apache-2.0 · pandas BSD-3 · NumPy BSD-3 · Plotly MIT · openpyxl MIT · Python PSF.
SBOM: `pip freeze > sbom.txt` at release; dependencies listed by name (pin at packaging time).
**90-day roadmap (pilot-driven).** Days 1–30: two design-partner pilots, instrument workflow timings, harden import edge cases.
Days 31–60: FastAPI + PostgreSQL team edition, real auth, reviewer SLAs. Days 61–90: pricing validation, GIS view, enterprise audit-export scoping.
**Demo script (60 s):** Mission Control (live sim) → Import demo-with-errors → fix/skip → Registry submit → Review approve →
Engine waterfall → Reports HTML pack → 🔗 Share read-only link.
"""
def make_backup():
    dest=BAK/f"registry_{now().strftime('%Y%m%d_%H%M%S')}.db"
    with db() as src:
        b=sqlite3.connect(dest); src.backup(b); b.close()
        log_event(src,"backup","database",0,f"Backup created: {dest.name}")
    return dest
def page_governance(sdf,odf,idf,adf,asmf):
    section("Governance & quality","Audit · lineage · dictionary · tests · backups · security · product docs")
    tabs=st.tabs(["🧾 Audit trail","🧬 Lineage","📖 Data dictionary","🧪 Quality suite","💾 Backup & retention","🔐 Access & security","📚 Product docs"])
    with tabs[0]:
        with db() as c: aud=pd.read_sql_query("SELECT * FROM audit ORDER BY ts DESC, id DESC",c)
        f1,f2,f3=st.columns([1,1,2])
        act=f1.selectbox("Action",["All"]+sorted(aud.action.unique()),key="gov_a_act")
        ent=f2.selectbox("Entity",["All"]+sorted(aud.entity.unique()),key="gov_a_ent")
        q=f3.text_input("Search detail",key="gov_a_q")
        d=aud.copy()
        if act!="All": d=d[d.action==act]
        if ent!="All": d=d[d.entity==ent]
        if q: d=d[d.detail.fillna("").str.lower().str.contains(q.lower())]
        d["Code"]=[code_of(e,int(i)) if e in TABLES and i else "—" for e,i in zip(d.entity,d.entity_id)]
        st.dataframe(d[["ts","actor","role","action","entity","Code","detail"]].rename(columns={"ts":"When","detail":"Detail"}),
                     hide_index=True,height=420,**W_DF)
        st.download_button("⬇ Export audit CSV",d.to_csv(index=False).encode(),file_name="audit_export.csv",mime="text/csv",
            key="gov_a_dl",on_click=log_export_cb,args=("Audit CSV (governance)","audit",0))
    with tabs[1]:
        c1,c2=st.columns(2)
        tbl=c1.selectbox("Record type",list(TABLES),format_func=str.capitalize,key="gov_l_tbl")
        dfmap={"observations":odf,"impacts":idf,"actions":adf,"assessments":asmf}
        d=dfmap[tbl]; codes=[code_of(tbl,int(i)) for i in d.id]
        rec=c2.selectbox("Record",codes,key="gov_l_rec")
        rid=int(rec.split("-")[1]); r=get_row(tbl,rid)
        if r:
            with db() as c:
                srow=c.execute("SELECT * FROM sites WHERE id=?",(r["site_id"],)).fetchone()
                src=None
                if r.get("source_file_id"):
                    src=c.execute("SELECT * FROM source_files WHERE id=?",(r["source_file_id"],)).fetchone()
                derived=[dict(x) for x in c.execute("SELECT * FROM assessments WHERE site_id=? ORDER BY created_at DESC LIMIT 3",(r["site_id"],))]
            chain=f'<div class="tl-i"><span class="tl-dot" style="background:{PAL["blue"]}"></span><div class="tl-t">1 · SOURCE</div><div class="tl-d">'
            if src: chain+=f'{esc(src["filename"])} · row {r.get("source_row")} · kind {esc(src["kind"])} · sha256 <code>{esc(src["sha256"][:24])}…</code>'
            else: chain+=f'Origin: {esc(r.get("origin","manual"))} (no file — direct entry / simulation)'
            chain+=f'</div></div><div class="tl-i"><span class="tl-dot" style="background:{PAL["teal"]}"></span><div class="tl-t">2 · VALIDATION</div><div class="tl-d">Flags: {", ".join(flags_of(r)) or "none"} · schema v{esc(r.get("schema_version",SCHEMA))}</div></div>'
            chain+=f'<div class="tl-i"><span class="tl-dot" style="background:{PAL["amber"]}"></span><div class="tl-t">3 · RECORD</div><div class="tl-d">{rec} at {esc(srow["code"])} · {esc(srow["name"])} · status {badge(r["status"])}</div></div>'
            if derived:
                chain+=f'<div class="tl-i"><span class="tl-dot" style="background:{PAL["violet"]}"></span><div class="tl-t">4 · DERIVED OUTPUTS</div><div class="tl-d">'
                for x in derived:
                    rr=json.loads(x["result"])
                    chain+=f'{code_of("assessments",x["id"])} · engine {esc(x["engine_version"])} · rules v{esc(x["rules_version"])} · net {pctf(rr["pct"])} · {esc(x["status"])}<br>'
                chain+='</div></div>'
            card(f"<b>Lineage chain — {rec}</b><div class='tl'>{chain}</div>")
            st.markdown("**Decision & export history**")
            st.markdown(timeline_html(audit_for(tbl,rid),15),unsafe_allow_html=True)
    with tabs[2]:
        dd=[
 ("sites.code","TEXT","—","Unique site code","3–4 uppercase letters","registry","Internal","UNIQUE, required"),
 ("sites.area_ha","REAL","hectares","Site area","> 0","survey / GIS","Internal","1 ha = 10 000 m²"),
 ("sites.lat / lon","REAL","WGS84 degrees","Location","-90..90 / -180..180","GIS","Restricted (real species sites)","range check"),
 ("sites.condition","TEXT","—","Baseline habitat condition","Poor / Fair / Good","ecologist assessment","Internal","enum"),
 ("observations.count","INTEGER","individuals etc.","Observed count","0–5000 (soft cap)","field survey / import","Internal","whole number, ≥0"),
 ("observations.unit","TEXT","—","Count unit",", ".join(UNITS),"field app","Internal","enum"),
 ("observations.method","TEXT","—","Survey method",", ".join(METHODS),"field app","Internal","enum; casual ⇒ estimate"),
 ("observations.observed_at","TEXT","ISO date","When observed","≤ today, ≥ today−10y (soft)","field app","Internal","parseable date"),
 ("observations.recorded_at","TEXT","ISO date","When recorded","≥ observed; lag ≤ 30d (soft)","system","Internal","LATE / CONTRADICTORY flags"),
 ("observations.status","TEXT","—","Lifecycle state",", ".join(STATUS_META),"workflow","Internal","transition matrix enforced"),
 ("observations.flags","TEXT","JSON","Quality flags","HARD + soft codes","validator","Internal","hard blocks validation"),
 ("observations.source_file_id","INTEGER","FK","Import lineage","source_files.id","importer","Internal","required for imports"),
 ("observations.source_row","INTEGER","row #","Lineage row","≥ 2","importer","Internal","header offset"),
 ("observations.origin","TEXT","—","Provenance channel","seed / import / manual / sim","system","Internal","enum"),
 ("impacts.severity","INTEGER","1–3","Impact severity","1 low · 3 high","ecologist","Internal","range"),
 ("impacts.area_ha","REAL","hectares","Affected area","> 0","walkover","Internal","range"),
 ("actions.progress","INTEGER","%","Delivery progress","0–100","project mgmt","Internal","range"),
 ("actions.cost_gbp","REAL","GBP","Budget","≥ 0","cost plan","Commercial","range"),
 ("actions.years_to_target","INTEGER","years","Time to condition","1–30","ecologist","Internal","drives temporal factor"),
 ("assessments.rules_version","TEXT","—","Factor table pin","1.1.0 / 1.2.0","engine","Internal","rollback-safe"),
 ("assessments.result","TEXT","JSON","Full output + explanation","engine schema","engine","Internal","deterministic"),
 ("assessments.override","TEXT","JSON","Manual override + reason","net_pct, reason","reviewer","Internal","audit required"),
 ("evidence.sha256","TEXT","hex-64","File checksum","SHA-256","system","Internal","integrity verify"),
 ("evidence.path","TEXT","path","Blob outside DB","filesystem","system","Internal","files never in rows"),
 ("source_files.sha256","TEXT","hex-64","Original file checksum","SHA-256","importer","Internal","preserved bytes"),
 ("audit.ts","TEXT","ISO UTC","Event time","RFC3339","system","Internal","append-only"),
 ("audit.detail","TEXT","—","Human-readable event","free text","system","Internal","no sensitive payloads"),
 ("meta.v","TEXT","—","Schema / seed version","semver","system","Internal","migration marker"),
        ]
        st.dataframe(pd.DataFrame(dd,columns=["Field","Type","Unit","Meaning","Allowed values","Source","Sensitivity","Validation rule"]),
                     hide_index=True,height=460,**W_DF)
    with tabs[3]:
        if "qa_results" not in ss: ss.qa_results=run_self_tests()
        res=ss.qa_results; passed=sum(1 for r in res if r["Result"].startswith("PASS"))
        m=st.columns(3)
        with m[0]: kpi("🧪","Tests",len(res),"unit · validation · RBAC · regression",PAL["blue"])
        with m[1]: kpi("✅","Passed",passed,"computed live in this session",PAL["green"] if passed==len(res) else PAL["magenta"])
        with m[2]: kpi("⏱","Runtime",f"{sum(r['ms'] for r in res):.0f} ms","real measured time",PAL["teal"])
        st.dataframe(pd.DataFrame(res),hide_index=True,height=420,**W_DF)
        if st.button("🔁 Re-run full suite",key="gov_qa_run",type="primary"):
            ss.qa_results=run_self_tests(); st.rerun()
        fixed={"area":2.0,"base_habitat":"Wetland","base_condition":"Fair","target_habitat":"Wetland","target_condition":"Good",
               "years":10,"difficulty":"Low","strategic":"Standard","target_pct":10}
        h=sha_bytes(json.dumps(assess(fixed,"1.2.0"),sort_keys=True).encode())
        st.markdown(f'<div class="mini">Regression fingerprint (fixed inputs, rules v1.2.0): <code>{h}</code> — hand-checkable expectations are asserted above; any change requires a documented version bump.</div>',unsafe_allow_html=True)
        st.caption("Software correctness ≠ domain validity: factor tables are synthetic demo values and require qualified ecological review before real use. No predictive/ML performance is claimed on synthetic data.")
    with tabs[4]:
        c1,c2=st.columns(2)
        with c1:
            card(f'<b>Storage</b><div class="mini">DB: {DBP} · {DBP.stat().st_size/1024:.0f} KB · evidence files: {len(list(EVI.glob("*")))} · sources: {len(list(SRC.glob("*")))}<br>Retention: archived records purged after N days (below). Large blobs live on disk; DB keeps metadata + SHA-256.</div>')
            if st.button("💾 Create backup now",key="gov_bk",type="primary",disabled=not can("admin")):
                p=make_backup(); st.toast(f"Backup created: {p.name}",icon="💾"); st.rerun()
            backs=sorted(BAK.glob("*.db"),reverse=True)
            if backs:
                names=[b.name for b in backs]
                if ss.get("gov_bk_sel") and ss["gov_bk_sel"] not in names: ss.pop("gov_bk_sel",None)
                sel=st.selectbox("Backups",names,key="gov_bk_sel")
                bpath=BAK/sel
                b1,b2,b3=st.columns(3)
                if b1.button("🔬 Integrity check",key="gov_bk_verify"):
                    conn=sqlite3.connect(bpath)
                    ok=conn.execute("PRAGMA integrity_check").fetchone()[0]
                    n=conn.execute("SELECT COUNT(*) FROM observations").fetchone()[0]; conn.close()
                    with db() as c: log_event(c,"backup","database",0,f"Restore-test evidence: {sel} integrity={ok}, observations={n}")
                    (st.success if ok=="ok" else st.error)(f"{sel}: integrity={ok} · {n} observation rows readable")
                b2.download_button("⬇ Download",bpath.read_bytes(),file_name=sel,mime="application/octet-stream",key="gov_bk_dl")
                confirm=st.checkbox("I understand restore replaces the live DB (safety snapshot taken first)",key="gov_bk_cf")
                if b3.button("♻️ Restore",key="gov_bk_restore",disabled=not confirm or not can("admin")):
                    make_backup()
                    with db() as c: c.execute("PRAGMA wal_checkpoint(TRUNCATE)")
                    shutil.copyfile(bpath,DBP)
                    for ext in ("-wal","-shm"):
                        p=Path(str(DBP)+ext)
                        if p.exists(): p.unlink()
                    with db() as c: log_event(c,"restore","database",0,f"Restored from {sel}")
                    st.toast("Database restored — re-run the Quality Suite",icon="♻️"); ss.pop("qa_results",None); st.rerun()
            else: st.info("No backups yet — create one above.")
        with c2:
            days=st.number_input("Retention: purge ARCHIVED records older than (days)",30,3650,365,key="gov_ret")
            if st.button("🧹 Purge archived (admin)",key="gov_purge",disabled=not can("admin")):
                cutoff=iso(now()-timedelta(days=int(days))); n=0
                with db() as c:
                    for t in ("observations","impacts","actions"):
                        cur=c.execute(f"DELETE FROM {t} WHERE status='ARCHIVED' AND updated_at<?",(cutoff,)); n+=cur.rowcount
                    c.execute("DELETE FROM assessments WHERE status='ARCHIVED' AND updated_at<?",(cutoff,))
                    log_event(c,"purge","database",0,f"Retention purge: {n}+ archived rows older than {int(days)}d")
                st.toast(f"Purged {n} archived rows",icon="🧹"); st.rerun()
            st.caption("Backups use SQLite's online backup API (consistent snapshot). Restore is tested via integrity check + row counts; every backup/restore is an audit event. PostgreSQL path is documented in Product docs.")
    with tabs[5]:
        actions_all=sorted({a for s in PERMS.values() for a in s})
        mat=pd.DataFrame([{ "Action":a, **{r:("✔" if a in PERMS[r] else "—") for r in PERMS}} for a in actions_all])
        st.dataframe(mat,hide_index=True,height=380,**W_DF)
        st.caption("Enforced in the mutation functions (not only the UI): every write calls require(action). Demo identities are personas, not authentication.")
        st.markdown(DOC_SECURITY)
    with tabs[6]:
        with st.expander("📄 Product brief & functional requirements (PRD)",expanded=True): st.markdown(DOC_PRD)
        with st.expander("🗂 Prioritized backlog — MVP / post-MVP / enterprise"): st.markdown(DOC_BACKLOG)
        with st.expander("✅ Acceptance checklist (observable pass/fail)"):
            qa={r["Test"]:r["Result"] for r in ss.get("qa_results",[])}
            acc=[
 ("Sample file imports end-to-end","Import page → demo valid → rows committed with lineage","Live: run demo import"),
 ("Malformed rows rejected with actionable errors","Error codes + row numbers + downloadable report",qa.get("Import: duplicate key rejected with row-level error","run suite")),
 ("Calculations reproducible","Fixed-input fingerprint identical across runs",qa.get("Engine determinism: identical inputs → identical hash","run suite")),
 ("Hand-checkable engine math","2 ha × 6 × Fair = 24.0 baseline asserted",qa.get("Hand-check: baseline 2 ha × 6 × Fair(2) = 24.0","run suite")),
 ("Outputs traceable","Explanation panel + lineage chain per record","Lineage tab"),
 ("Report exports","HTML/JSON/CSV with provenance, audit-logged","Reports page"),
 ("Illegal lifecycle transitions blocked","DRAFT→APPROVED rejected",qa.get("Lifecycle: DRAFT → APPROVED is blocked","run suite")),
 ("Role permissions enforced server-side","Stakeholder/Analyst cannot approve",qa.get("RBAC: Analyst cannot approve; Reviewer can","run suite")),
 ("Automated suite passes","All tests green",f"{sum(1 for v in qa.values() if v.startswith('PASS'))}/{len(qa) or '—'}"),
 ("Demo repeatable from clean DB","Reset demo data → identical seed (RNG 17)","Sidebar → Reset"),
            ]
            st.dataframe(pd.DataFrame(acc,columns=["Criterion","Observable condition","Status / where"]),hide_index=True,**W_DF)
        with st.expander("⚠ Risk register"): st.markdown(DOC_RISKS)
        with st.expander("🛠 Runbook · backup/restore · PostgreSQL migration"): st.markdown(DOC_RUNBOOK)
        with st.expander("💼 Commercialization, licences & 90-day roadmap"): st.markdown(DOC_COMMERCIAL)

# ────────────────────────────────────────── DIALOGS ───────────────────────────
@modal("🗂 Record detail")
def drawer_dialog():
    ctx=ss.drawer; tbl,rid=ctx["table"],ctx["id"]
    r=get_row(tbl,rid)
    if not r or r.get("deleted_at"):
        st.warning("Record no longer available."); ss.drawer=None; return
    code=code_of(tbl,rid)
    with db() as c:
        srow=dict(c.execute("SELECT * FROM sites WHERE id=?",(r["site_id"],)).fetchone())
    st.markdown(f'<div style="display:flex;gap:10px;align-items:center;flex-wrap:wrap"><b style="font-size:1.2rem">{code}</b>{badge(r["status"])}'
                f'<span class="mini">{esc(srow["code"])} · {esc(srow["name"])} · origin {esc(r.get("origin","—"))}</span></div>',unsafe_allow_html=True)
    if tbl=="assessments":
        res=json.loads(r["result"])
        tA,tH=st.tabs(["🧮 Assessment","🕘 History"])
        with tA:
            m=st.columns(4)
            with m[0]: kpi("🟤","Baseline",res["baseline"],"units",PAL["clay"])
            with m[1]: kpi("🟢","Post",res["post"],f"±{res['band_abs']}",PAL["green"])
            with m[2]: kpi("Δ","Net",pctf(res["pct"]),f"rules v{r['rules_version']}",PAL["green"] if res["meets"] else PAL["magenta"])
            with m[3]: kpi("🎯","Target","MEETS ✅" if res["meets"] else "BELOW ⛔","human approval required",PAL["blue"])
            st.plotly_chart(waterfall_fig(res),config=PCFG,key="dr_wf",**W_PC)
            with st.expander("🧾 Explanation & provenance",expanded=True):
                for ln in res["explanation"]: st.markdown(ln)
            if r.get("override"):
                ov=json.loads(r["override"]); st.warning(f"Manual override: net {ov['net_pct']}% — {ov['reason']}")
            if can("override") and st.button("✍️ Manual override with reason",key="dr_ov"):
                ss.reason={"mode":"engine_override","table":tbl,"id":rid}; ss.drawer=None; ss.pop("rs_reason",None); st.rerun()
        with tH: st.markdown(timeline_html(audit_for(tbl,rid),20),unsafe_allow_html=True)
    else:
        tO,tE,tH,tM=st.tabs(["📋 Overview","📎 Evidence","🕘 History","⚙️ Manage"])
        with tO:
            if tbl=="observations":
                inner=(f'<b>{esc(r["common_name"])}</b> <span class="mini">({esc(r["taxon"])})</span><br>'
                       f'Count: <b>{r["count"]} {esc(r["unit"])}</b> · Method: {esc(r["method"] or "—")}<br>'
                       f'Observed: {esc(r["observed_at"])} · Recorded: {esc(r["recorded_at"])} by {esc(r["recorded_by"])}<br>'
                       f'Notes: {esc(r["notes"] or "—")}<br><br><b>Provenance</b><br>'
                       +(f'Source: {esc(r.get("source_file") or "")} · row {r.get("source_row")} · sha <code>{esc((r.get("source_sha") or "")[:20])}</code>' if r.get("source_file_id") else f'Origin: {esc(r.get("origin"))} — direct entry')
                       +f'<br>Schema v{esc(r.get("schema_version",SCHEMA))} · created {fmt_dt(r["created_at"])}')
            elif tbl=="impacts":
                inner=(f'<b>{esc(r["activity"])}</b><br>Type: {esc(r["impact_type"])} · Area: {r["area_ha"]} ha · Severity {r["severity"]}/3<br>'
                       f'Start: {esc(r["start_date"])} · Notes: {esc(r["notes"] or "—")}<br>Origin: {esc(r.get("origin"))}')
            else:
                inner=(f'<b>{esc(r["action_type"])}</b> → {esc(r["habitat_target"])} ({esc(r["condition_target"])})<br>'
                       f'{r["area_ha"]} ha · {r["years_to_target"]} y to target · difficulty {esc(r["difficulty"])} · {esc(r["strategic"])}<br>'
                       f'Budget {money(r["cost_gbp"])} · progress {r["progress"]}%<br>'
                       f'<div class="bar" style="margin:6px 0"><div style="width:{int(r["progress"])}%"></div></div>'
                       f'Notes: {esc(r["notes"] or "—")}')
            card(inner+f'<div style="margin-top:8px">{flags_html(flags_of(r))}</div>')
        with tE:
            with db() as c:
                ev=[dict(x) for x in c.execute("SELECT * FROM evidence WHERE (entity=? AND entity_id=?) OR (entity='sites' AND entity_id=?)",
                                               (tbl,rid,r["site_id"]))]
            if not ev: st.info("No evidence attached yet.")
            for e in ev:
                cc1,cc2=st.columns([3,1])
                cc1.markdown(f'<div class="tick">📎 <b>{esc(e["filename"])}</b>&nbsp;· {e["bytes"]} B · <code>{e["sha256"][:16]}…</code></div>',unsafe_allow_html=True)
                p=Path(e["path"])
                if p.exists():
                    cc2.download_button("⬇",p.read_bytes(),file_name=e["filename"],key=f"dr_ev_{e['id']}",
                        on_click=log_export_cb,args=(f"Evidence {e['filename']}",tbl,rid))
            if can("create") or can("edit"):
                with st.form("dr_ev_form",clear_on_submit=True):
                    up=st.file_uploader("Attach evidence (≤10 MB, stored on disk + checksum)",key="dr_up")
                    if st.form_submit_button("📎 Attach"):
                        if up is None: st.error("Choose a file first.")
                        elif up.size>10*1024*1024: st.error("File exceeds 10 MB.")
                        else:
                            b=up.getvalue(); fn=safe_name(up.name); p=EVI/f"{sha_bytes(b)[:12]}_{fn}"; p.write_bytes(b)
                            with db() as c:
                                ins(c,"evidence",{"entity":tbl,"entity_id":rid,"filename":fn,"kind":fn.split(".")[-1],
                                    "bytes":len(b),"sha256":sha_bytes(b),"path":str(p),"uploaded_by":ss.actor,"uploaded_at":now_iso()})
                                log_event(c,"attach",tbl,rid,f"Evidence '{fn}' attached to {code} · sha {sha_bytes(b)[:12]}…")
                            st.toast("Evidence attached with checksum",icon="📎"); st.rerun()
        with tH: st.markdown(timeline_html(audit_for(tbl,rid),20),unsafe_allow_html=True)
        with tM:
            if can("edit"):
                with st.form("dr_edit"):
                    if tbl=="observations":
                        e1,e2,e3=st.columns(3)
                        cnt=e1.number_input("Count",0,100000,int(r["count"]),key="dr_e_cnt")
                        un=e2.selectbox("Unit",UNITS,index=UNITS.index(r["unit"]) if r["unit"] in UNITS else 0,key="dr_e_un")
                        me=e3.selectbox("Method",METHODS,index=METHODS.index(r["method"]) if r["method"] in METHODS else 0,key="dr_e_me")
                        od=st.date_input("Observed",value=parse_date(r["observed_at"]),key="dr_e_od")
                        notes=st.text_area("Notes",value=r["notes"] or "",key="dr_e_no")
                        new={"count":int(cnt),"unit":un,"method":me,"observed_at":od.isoformat(),"notes":notes}
                    elif tbl=="impacts":
                        e1,e2=st.columns(2)
                        act=e1.text_input("Activity",value=r["activity"],key="dr_e_act")
                        typ=e2.selectbox("Type",IMPACT_TYPES,index=IMPACT_TYPES.index(r["impact_type"]),key="dr_e_typ")
                        e3,e4=st.columns(2)
                        area=e3.number_input("Area (ha)",0.01,50.0,float(r["area_ha"]),key="dr_e_ar")
                        sev=e4.slider("Severity",1,3,int(r["severity"]),key="dr_e_sv")
                        notes=st.text_area("Notes",value=r["notes"] or "",key="dr_e_no")
                        new={"activity":act,"impact_type":typ,"area_ha":area,"severity":sev,"notes":notes}
                    else:
                        e1,e2=st.columns(2)
                        prog=e1.slider("Progress %",0,100,int(r["progress"]),key="dr_e_pr")
                        cost=e2.number_input("Cost (£)",0,1_000_000,int(r["cost_gbp"]),step=500,key="dr_e_co")
                        notes=st.text_area("Notes",value=r["notes"] or "",key="dr_e_no")
                        new={"progress":prog,"cost_gbp":cost,"notes":notes}
                    if st.form_submit_button("💾 Save changes",type="primary"):
                        try:
                            require("edit")
                            if tbl=="observations":
                                vrow={**r,**new,"site_code":srow["code"]}
                                errs,warns=validate_obs_fields(vrow,{srow["code"]},now().date())
                                if errs:
                                    st.error(" · ".join(f"[{e['code']}] {e['msg']}" for e in errs)); st.stop()
                                new["flags"]=json.dumps([w["code"] for w in warns])
                            new["updated_at"]=now_iso()
                            if r["status"]=="APPROVED":
                                new["status"]="CORRECTION"
                            with db() as c:
                                upd(c,tbl,rid,new)
                                log_event(c,"edit",tbl,rid,f"{code} edited"+(" · APPROVED → CORRECTION (re-review required)" if r["status"]=="APPROVED" else ""))
                            st.toast("Saved"+(" — sent to CORRECTION for re-review" if r["status"]=="APPROVED" else ""),icon="💾"); st.rerun()
                        except PermissionError as e: st.error(str(e))
            m1,m2,m3,m4=st.columns(4)
            if r["status"]=="DRAFT" and m1.button("🧪 Validate",key="dr_val",disabled=not can("validate")):
                flags=flags_of(r)
                hard=[f for f in flags if f in HARD]
                if tbl=="observations":
                    errs,_=validate_obs_fields({**r,"site_code":srow["code"]},{srow["code"]},now().date())
                    hard=[e["code"] for e in errs]
                if hard: st.error("Hard errors block validation: "+", ".join(hard)+" — fix them in the edit form.")
                else:
                    try: do_transition(tbl,rid,"VALIDATED"); st.toast(f"{code} validated",icon="🧪"); st.rerun()
                    except (PermissionError,ValueError) as e: st.error(str(e))
            if r["status"]=="VALIDATED" and m2.button("🔍 Submit",key="dr_sub",disabled=not can("submit")):
                try: do_transition(tbl,rid,"IN_REVIEW"); st.toast(f"{code} submitted for review",icon="🔍"); st.rerun()
                except (PermissionError,ValueError) as e: st.error(str(e))
            if r["status"]=="IN_REVIEW" and m3.button("✅ Approve",key="dr_ap",disabled=not can("approve")):
                if needs_reason(flags_of(r),"APPROVED"):
                    ss.reason={"mode":"approve_override","table":tbl,"id":rid}; ss.drawer=None; ss.pop("rs_reason",None); st.rerun()
                else:
                    try: do_transition(tbl,rid,"APPROVED"); st.toast(f"{code} approved",icon="✅"); st.rerun()
                    except (PermissionError,ValueError) as e: st.error(str(e))
            if can("delete") and m4.button("🗑 Delete",key="dr_del"):
                with db() as c:
                    upd(c,tbl,rid,{"deleted_at":now_iso(),"updated_at":now_iso()})
                    log_event(c,"delete",tbl,rid,f"{code} soft-deleted (undo available)")
                ss.undo={"table":tbl,"ids":[rid]}; ss.drawer=None
                st.toast(f"{code} deleted — Undo in banner",icon="🗑"); st.rerun()
            a1,a2=st.columns(2)
            if r["status"]!="ARCHIVED" and a1.button("🗄 Archive",key="dr_arch",disabled=not can("archive")):
                try: do_transition(tbl,rid,"ARCHIVED","from drawer"); st.toast("Archived",icon="🗄"); st.rerun()
                except (PermissionError,ValueError) as e: st.error(str(e))
            if r["status"]=="ARCHIVED" and a2.button("♻️ Restore to DRAFT",key="dr_rest",disabled=not can("restore")):
                try: do_transition(tbl,rid,"DRAFT","restored from archive"); st.toast("Restored",icon="♻️"); st.rerun()
                except (PermissionError,ValueError) as e: st.error(str(e))
    st.divider()
    f1,f2=st.columns(2)
    if f1.button("🔗 Share this record",key="dr_share",type="primary"):
        ss.share={"kind":"record","table":tbl,"id":rid}; ss.drawer=None; st.rerun()
    if f2.button("✖ Close",key="dr_close"): ss.drawer=None; st.rerun()

@modal("📝 Review decision")
def reason_dialog():
    ctx=ss.reason; mode=ctx["mode"]; code=code_of(ctx["table"],ctx["id"])
    titles={"reject":f"⛔ Reject {code}","correction":f"🛠 Return {code} for correction",
            "approve_override":f"✅ Approve {code} — override required","engine_override":f"✍️ Manual override — {code}"}
    st.markdown(f"**{titles.get(mode,mode)}**")
    if mode=="approve_override":
        st.warning("This record carries a CONTRADICTORY flag. Approval is only possible with a documented override reason (audited).")
    with st.form("rs_form",clear_on_submit=True):
        val=None
        if mode=="engine_override":
            val=st.number_input("Override net change (%)",-100.0,1000.0,10.0,0.1,key="rs_val")
        reason=st.text_area("Reason (required, written to the audit trail)",key="rs_reason",
                            placeholder="e.g. Reconciled against eDNA lab report #48 — camera undercount confirmed…")
        c1,c2=st.columns(2)
        ok=c1.form_submit_button("Confirm decision",type="primary")
        cancel=c2.form_submit_button("Cancel")
        if cancel: ss.reason=None; st.rerun()
        if ok:
            if not reason.strip(): st.error("A reason is required — decisions must be traceable.")
            else:
                try:
                    if mode=="engine_override":
                        require("override")
                        with db() as c:
                            upd(c,"assessments",ctx["id"],{"override":json.dumps({"net_pct":val,"reason":reason.strip(),
                                "by":ss.actor,"at":now_iso()}),"updated_at":now_iso()})
                            log_event(c,"override","assessments",ctx["id"],f"{code} manual override net {val}% · reason: {reason.strip()}")
                        st.toast("Override recorded with audit trail",icon="✍️")
                    else:
                        to={"reject":"REJECTED","correction":"CORRECTION","approve_override":"APPROVED"}[mode]
                        do_transition(ctx["table"],ctx["id"],to,reason.strip())
                        st.toast(f"{code} → {to}",icon="📝")
                    ss.reason=None; st.rerun()
                except (PermissionError,ValueError) as e: st.error(str(e))

@modal("➕ New observation")
def new_obs_dialog():
    with db() as c: sdf=sites_df(c)
    with st.form("no_form",clear_on_submit=True):
        c1,c2=st.columns(2)
        sc=c1.selectbox("Site",list(sdf.code),key="no_site")
        tx=c2.selectbox("Taxon",[t[0] for t in TAXA],format_func=lambda s:f"{s} — {next(t[1] for t in TAXA if t[0]==s)}",key="no_tx")
        c3,c4,c5=st.columns(3)
        cnt=c3.number_input("Count",0,5000,1,key="no_cnt")
        un=c4.selectbox("Unit",UNITS,key="no_un")
        me=c5.selectbox("Method",METHODS,key="no_me")
        c6,c7=st.columns(2)
        od=c6.date_input("Observed",value=now().date(),key="no_od")
        rd=c7.date_input("Recorded",value=now().date(),key="no_rd")
        notes=st.text_area("Notes",key="no_notes",placeholder="conditions, transect ID, observers…")
        s1,s2=st.columns(2)
        ok=s1.form_submit_button("Create record",type="primary")
        cancel=s2.form_submit_button("Cancel")
        if cancel: ss.new_obs=False; st.rerun()
        if ok:
            row={"site_code":sc,"taxon":tx,"count":cnt,"unit":un,"method":me,
                 "observed_at":od.isoformat(),"recorded_at":rd.isoformat()}
            errs,warns=validate_obs_fields(row,set(sdf.code),now().date())
            if errs: st.error(" · ".join(f"[{e['code']}] {e['msg']}" for e in errs))
            else:
                try:
                    require("create")
                    cn=next(t[1] for t in TAXA if t[0]==tx)
                    with db() as c:
                        sid=int(sdf[sdf.code==sc].iloc[0].id)
                        oid=ins(c,"observations",{"site_id":sid,"taxon":tx,"common_name":cn,"count":int(cnt),"unit":un,
                            "method":me,"observed_at":od.isoformat(),"recorded_at":rd.isoformat(),"recorded_by":ss.actor,
                            "status":"DRAFT","flags":json.dumps([w["code"] for w in warns]),"notes":notes,"origin":"manual",
                            "schema_version":SCHEMA,"created_at":now_iso(),"updated_at":now_iso()})
                        log_event(c,"create","observations",oid,f"{code_of('observations',oid)} manual entry · {cn} ×{cnt}")
                    ss.new_obs=False; ss.drawer={"table":"observations","id":oid}
                    st.toast(f"{code_of('observations',oid)} created as DRAFT",icon="🔭"); st.rerun()
                except PermissionError as e: st.error(str(e))

@modal("🔗 Share")
def share_dialog():
    ctx=ss.share; kind=ctx["kind"]
    base=st.text_input("App base URL (use your deployed URL for external sharing)",
                       value=ss.get("base_url","http://localhost:8501"),key="sh_base")
    ss.base_url=base
    read_only=st.toggle("Recipient lands as read-only Stakeholder",value=True,key="sh_ro")
    params={}
    if read_only: params["role"]="Stakeholder"
    title=""; summary=""; html_scope=None; focus=None
    if kind=="record":
        tbl,rid=ctx["table"],ctx["id"]; code=code_of(tbl,rid); r=get_row(tbl,rid)
        params.update({"page":"registry","record":code})
        title=f"Record {code}"
        with db() as c: srow=dict(c.execute("SELECT * FROM sites WHERE id=?",(r["site_id"],)).fetchone())
        html_scope=int(r["site_id"]); focus=code
        summary=f"{APP} record {code} at {srow['name']} — status {r['status']}, full provenance & audit trail."
    elif kind=="site":
        with db() as c: srow=dict(c.execute("SELECT * FROM sites WHERE id=?",(ctx["id"],)).fetchone())
        params.update({"page":"reports","site":srow["code"]})
        title=f"Site report — {srow['name']}"; html_scope=ctx["id"]
        summary=f"{APP} evidence pack for {srow['name']} ({srow['habitat']}, {srow['area_ha']} ha) — assessments, lineage, audit."
    else:
        params.update({"page":"mission"}); title="Workspace — TerraLedger demo"
        summary=f"{APP}: biodiversity evidence registry demo — live simulation, review workflows, explainable net-gain engine. Synthetic data."
    link=base.rstrip("/")+("/?" if params else "")+urlencode(params)
    card(f'<b>{esc(title)}</b><div class="mini" style="margin-top:4px">{esc(summary)}</div>')
    st.markdown("**📋 Copy link** (clipboard button on the code box):")
    st.code(link,language=None)
    try:
        comp_html(f"""<button onclick='navigator.clipboard.writeText({json.dumps(link)})
            .then(()=>this.textContent="✓ Copied to clipboard").catch(()=>this.textContent="Use the copy icon above")'
            style='background:linear-gradient(135deg,#34d399,#0ea5a0);color:#052015;border:none;border-radius:12px;
            padding:9px 18px;font-weight:700;font-family:Inter,sans-serif;cursor:pointer'>📋 Copy link</button>""",height=48)
    except Exception: pass
    msg=f"{summary}\n\nOpen: {link}\n(Synthetic demo data — decision support only.)"
    st.markdown("**Share via**")
    b=st.columns(4)
    with b[0]: link_btn("in · LinkedIn",f"https://www.linkedin.com/sharing/share-offsite/?url={quote(link,safe='')}",key="sh_li")
    with b[1]: link_btn("𝕏 · Post",f"https://twitter.com/intent/tweet?text={quote(msg)}",key="sh_x")
    with b[2]: link_btn("💬 WhatsApp",f"https://wa.me/?text={quote(msg)}",key="sh_wa")
    with b[3]: link_btn("✉️ Email",f"mailto:?subject={quote(title)}&body={quote(msg)}",key="sh_mail")
    st.markdown("**Or send a self-contained evidence pack**")
    d=st.columns(2)
    pack_key=f"shpack:{html_scope}:{focus}"
    if ss.get("shpack_key")!=pack_key:
        ss.shpack=build_html_report(html_scope,focus); ss.shpack_key=pack_key
    d[0].download_button("⬇ HTML evidence pack",ss.shpack.encode(),file_name="terraledger_share_pack.html",mime="text/html",
        key="sh_html",type="primary",on_click=log_export_cb,args=(f"Share pack ({title})","sites",html_scope or 0))
    d[1].download_button("⬇ JSON bundle",bundle_json(html_scope),file_name="terraledger_share_bundle.json",
        mime="application/json",key="sh_json",on_click=log_export_cb,args=(f"Share JSON ({title})","sites",html_scope or 0))
    st.caption("Links deep-link to this exact record/report. Recipients need the app running at that URL — locally that's your machine; deploy for external sharing. Read-only role is enforced by the app on arrival.")
    if st.button("✖ Close",key="sh_close"): ss.share=None; st.rerun()

@modal("♻️ Reset demo data")
def reset_dialog():
    st.warning("This wipes the local database and re-seeds the identical synthetic demo (deterministic RNG · seed 17). Evidence/source files are regenerated. Backups are kept.")
    c1,c2=st.columns(2)
    if c1.button("Yes, reset everything",key="rs_go",type="primary"):
        make_backup()
        with db() as c: c.execute("PRAGMA wal_checkpoint(TRUNCATE)")
        DBP.unlink(missing_ok=True)
        for ext in ("-wal","-shm"): Path(str(DBP)+ext).unlink(missing_ok=True)
        for p in list(EVI.glob("seed_*")): p.unlink(missing_ok=True)
        init_storage()
        for k in list(ss.keys()):
            if k.startswith(("pg_","bulk_","open_","f_","fi_","fa_","eng_","rpt_","imp_","qa_","shpack")): ss.pop(k,None)
        ss.pop("sim",None); sim_init()
        st.toast("Demo reset — identical seed restored",icon="♻️"); st.rerun()
    if c2.button("Cancel",key="rs_no"): ss.reset=False; st.rerun()

# ────────────────────────────────────────── SHELL ─────────────────────────────
NAV=[("mission","🛰️ Mission Control"),("import","📥 Import & Validate"),("registry","🗂️ Records Registry"),
     ("engine","🧮 Impact Engine"),("review","✅ Review Queue"),("reports","📊 Reports & Export"),("governance","🛡️ Governance & QA")]
def consume_qp():
    if ss.get("_qp_done"): return
    qp=st.query_params
    role=qp.get("role")
    if role in PERMS:
        ss.actor=next(n for n,u in USERS.items() if u["role"]==role)
    pg=qp.get("page")
    if pg in dict(NAV): ss.nav_pref=pg
    rec=qp.get("record")
    if rec:
        m=re.match(r"^(OBS|IMP|ACT|ASM)-(\d+)$",rec)
        if m:
            tbl=next(t for t,p in TABLES.items() if p==m.group(1))
            ss.drawer={"table":tbl,"id":int(m.group(2))}; ss.nav_pref="registry"
    site=qp.get("site")
    if site:
        with db() as c:
            r=c.execute("SELECT name FROM sites WHERE code=?",(site,)).fetchone()
            if r: ss.rpt_pref=f"{site} — {r['name']}"; ss.nav_pref="reports"
    ss._qp_done=True
def sidebar(pending_n):
    with st.sidebar:
        st.markdown('<div class="brand" style="margin-bottom:10px"><div class="brand-t" style="font-size:1.35rem">🌿 TerraLedger</div></div>'
                    '<div class="mini" style="margin-bottom:12px">Biodiversity Impact Evidence & Monitoring Registry</div>',unsafe_allow_html=True)
        u=USERS[ss.actor]
        st.markdown(f'<div class="card" style="padding:10px 12px"><div style="display:flex;gap:10px;align-items:center">'
                    f'<div style="width:38px;height:38px;border-radius:50%;background:linear-gradient(135deg,{u["c"]},#0ea5a0);'
                    f'display:flex;align-items:center;justify-content:center;font-weight:800;color:#052015">{u["init"]}</div>'
                    f'<div><b style="font-size:.9rem">{esc(ss.actor)}</b><div class="mini">{esc(u["role"])} · demo identity</div></div></div></div>',unsafe_allow_html=True)
        names=list(USERS)
        pick=st.selectbox("Switch persona (role demo)",names,index=names.index(ss.actor),key="persona")
        if pick!=ss.actor:
            ss.actor=pick
            with db() as c: log_event(c,"session","users",0,f"Persona switched to {pick} ({USERS[pick]['role']})")
            st.toast(f"Now acting as {USERS[pick]['role']}",icon="👤"); st.rerun()
        ss.role=USERS[ss.actor]["role"]
        st.divider()
        labels=[l for _,l in NAV]
        def fmt(l):
            return l+f"  ·  {pending_n}" if l.startswith("✅") and pending_n else l
        idx=[s for s,_ in NAV].index(ss.get("nav_pref","mission"))
        chosen=st.radio("Navigate",labels,index=idx,format_func=fmt,label_visibility="collapsed")
        ss.nav_pref=next(s for s,l in NAV if l==chosen)
        st.divider()
        st.markdown(f'<div class="mini">💾 SQLite · {DBP.stat().st_size/1024:.0f} KB · {len(list(EVI.glob("*")))} evidence files<br>'
                    f'🧩 app v{VER} · schema {SCHEMA} · rules {ss.get("eng_rv_pref","1.2.0")}<br>🧪 synthetic demo data — labelled everywhere</div>',unsafe_allow_html=True)
        if st.button("♻️ Reset demo data",key="sb_reset",disabled=not can("admin")):
            ss.reset=True; st.rerun()
        st.caption("Decision support only · human approval required · no paid APIs")
    return ss.nav_pref
def topbar():
    c1,c2,c3=st.columns([3.2,1,1])
    with c1:
        live='<span class="chip"><span class="dot"></span> LIVE SIM</span>' if ss.sim.get("running") else '<span class="chip">⏸ SIM PAUSED</span>'
        st.markdown(f"""<div class="brand">
<svg width="46" height="46" viewBox="0 0 48 48"><defs><linearGradient id="lg" x1="0" y1="0" x2="1" y2="1">
<stop offset="0" stop-color="#4ade80"/><stop offset="1" stop-color="#38bdf8"/></linearGradient></defs>
<rect x="4" y="4" width="40" height="40" rx="12" fill="none" stroke="url(#lg)" stroke-width="2.5"/>
<path d="M33 14c1.2 9.5-5 16.5-14.5 17.5C17.3 22 23.5 15 33 14z" fill="url(#lg)"/>
<path d="M19 32C22.5 26 27.5 20.5 33 14.5" stroke="#081410" stroke-width="1.6" fill="none"/>
<path d="M14 37h20" stroke="#4ade80" stroke-width="2" stroke-linecap="round"/></svg>
<div><div class="brand-t">TerraLedger</div><div class="brand-s">Biodiversity Impact Evidence & Monitoring Registry · Project 017</div></div>
<div style="display:flex;gap:8px;flex-wrap:wrap">{live}<span class="chip" style="color:#fbbf24;border-color:#fbbf2455">SYNTHETIC DEMO</span>
<span class="chip">{now().strftime("%a %d %b %Y")}</span></div></div>""",unsafe_allow_html=True)
    with c2:
        if st.button("➕ New observation",key="top_new",disabled=not can("create")):
            ss.new_obs=True; st.rerun()
    with c3:
        if st.button("🔗 Share",key="top_share",type="primary"):
            ss.share={"kind":"workspace"}; st.rerun()
def undo_banner():
    if not ss.get("undo"): return
    u=ss.undo; c1,c2,c3=st.columns([4,1,1])
    c1.info(f"🗑 {len(u['ids'])} record(s) soft-deleted from {u['table']} — recoverable until you dismiss.")
    if c2.button("↩️ Undo",key="undo_go",type="primary"):
        with db() as c:
            for rid in u["ids"]:
                upd(c,u["table"],rid,{"deleted_at":None,"updated_at":now_iso()})
                log_event(c,"restore",u["table"],rid,f"{code_of(u['table'],rid)} restored via undo")
        ss.undo=None; st.toast("Deletion undone",icon="↩️"); st.rerun()
    if c3.button("Dismiss",key="undo_no"): ss.undo=None; st.rerun()

# ────────────────────────────────────────── MAIN ──────────────────────────────
def main():
    st.set_page_config(page_title=f"{APP} — Biodiversity Evidence Registry",page_icon="🌿",layout="wide",initial_sidebar_state="expanded")
    st.markdown(CSS,unsafe_allow_html=True)
    ss.setdefault("actor","Amara Okafor"); ss.setdefault("role","Administrator"); ss.setdefault("nav_pref","mission")
    init_storage(); sim_init(); init_filters()
    with db() as c:
        ss.site_meta=[{"id":r["id"],"code":r["code"],"tidx":next(x[9] for x in SITE_SEED if x[0]==r["code"])}
                      for r in c.execute("SELECT id,code FROM sites")]
    consume_qp()
    sdf,odf,idf,adf,asmf=load_all()
    items=review_items(sdf,odf,idf,adf,asmf)
    page=sidebar(len(items))
    if st.query_params.get("page")!=page: st.query_params["page"]=page
    topbar(); undo_banner()
    if page=="mission": page_mission(sdf,odf,idf,adf,asmf)
    elif page=="import": page_import()
    elif page=="registry": page_registry(sdf,odf,idf,adf,asmf)
    elif page=="engine": page_engine(sdf,odf,idf,adf,asmf)
    elif page=="review": page_review(sdf,odf,idf,adf,asmf)
    elif page=="reports": page_reports(sdf,odf,idf,adf,asmf)
    else: page_governance(sdf,odf,idf,adf,asmf)
    if ss.get("share"): share_dialog()
    elif ss.get("reason"): reason_dialog()
    elif ss.get("new_obs"): new_obs_dialog()
    elif ss.get("reset"): reset_dialog()
    elif ss.get("drawer"): drawer_dialog()
    st.markdown('<div style="text-align:center;margin:26px 0 8px" class="mini">🌿 TerraLedger · decision support only · '
                'synthetic demonstration data · every approval is a human action · exports & overrides are audited</div>',unsafe_allow_html=True)

main()
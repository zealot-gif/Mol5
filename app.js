// === 分子與反應機構資料結構 ===
let atoms = [];  // { id, x, y, el, charge, lonePairs, implicitH }
let bonds = [];  // { a1, a2, order }
let arrows = []; // { x1, y1, x2, y2, curve }
let history = [];
let redoStack = [];

// 預設工具：移動分子 (move)
let currentMode = "move";
let currentBondOrder = 1;
let currentRingType = "polygon";
let currentSubstituentType = "CH3";
let currentChargeVal = 1;
let currentElement = "C";
let zoom = 1.0;

// 2D 氫原子展開顯示切換狀態
let showHydrogens2D = false;

let hoverAtom = null;
let hoverBond = null;
let hoverArrow = null;
let selectedArrow = null;
let hoverPos = null;

let dragStartAtom = null;
let dragArrowStart = null;
let dragArrowCurve = false;
let dragRingStart = null;
let dragRingAttachAtom = null;
let dragRingSides = 6;
let dragRingAngle = -Math.PI / 2;

// 單一分子獨立移動 vs. 畫布整體平移狀態
let dragMoveLast = null;
let dragMoveAtomIds = null;

// 橡皮擦按住拖曳連續擦除狀態
let isErasingDrag = false;
let eraseHasSavedState = false;
let lastErasePos = null;

let dragPos = null;

let isRightRotating = false;
let rotateCenter = { x: 0, y: 0 };
let rotateScreenCenter = { x: 0, y: 0 };
let lastRotateAngle = 0;
let lastRightDist = 0;

let isTwoFingerGesture = false;
let lastTouchAngle = 0;
let lastTouchDist = 0;
let lastTouchClient = { x: 0, y: 0 };
let preTouchSnapshot = null;

let desktopShow3D = true;
let mobileActivePane = "2d";

let viewer3D = null;
let currentSdfData = "";

let base3DAtoms = [];
let base3DBonds = [];
let rotatableBonds = [];

const ATOM_COLORS = {
  C: "#1e293b", H: "#475569", N: "#2563eb", O: "#dc2626",
  S: "#d97706", P: "#ea580c", F: "#16a34a", Cl: "#16a34a",
  Br: "#991b1b", I: "#7e22ce", B: "#be185d", Mg: "#059669", Li: "#7c3aed"
};

const MAX_COVALENT_BONDS = {
  H: 1, He: 0,
  Li: 1, Be: 2, B: 3, C: 4, N: 3, O: 2, F: 1, Ne: 0,
  Na: 1, Mg: 2, Al: 3, Si: 4, P: 5, S: 6, Cl: 1, Ar: 0,
  K: 1, Ca: 2, Sc: 3, Ti: 4, V: 5, Cr: 6, Mn: 7, Fe: 6, Co: 6, Ni: 4, Cu: 4, Zn: 4,
  Ga: 3, Ge: 4, As: 5, Se: 6, Br: 1, Kr: 2,
  Rb: 1, Sr: 2, Y: 3, Zr: 4, Nb: 5, Mo: 6, Tc: 7, Ru: 8, Rh: 6, Pd: 4, Ag: 2, Cd: 4,
  In: 3, Sn: 4, Sb: 5, Te: 6, I: 1, Xe: 4,
  Cs: 1, Ba: 2, Hf: 4, Ta: 5, W: 6, Re: 7, Os: 8, Ir: 6, Pt: 6, Au: 4, Hg: 4,
  Tl: 3, Pb: 4, Bi: 5, At: 1, Rn: 0
};

const NEUTRAL_VALENCE = {
  H: 1,
  Li: 1, Be: 2, B: 3, C: 4, N: 3, O: 2, F: 1,
  Na: 1, Mg: 2, Al: 3, Si: 4, P: 3, S: 2, Cl: 1,
  K: 1, Ca: 2, Ga: 3, Ge: 4, As: 3, Se: 2, Br: 1,
  Rb: 1, Sr: 2, In: 3, Sn: 4, Sb: 3, Te: 2, I: 1,
  Cs: 1, Ba: 2, Tl: 3, Pb: 4, Bi: 3, At: 1
};

const SUBSCRIPT_DIGITS = {
  "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄",
  "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉"
};

const SUPERSCRIPT_CHARS = {
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
  "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
  "+": "⁺", "-": "⁻"
};

function toSubscript(num) {
  return String(num)
    .split("")
    .map((ch) => SUBSCRIPT_DIGITS[ch] || ch)
    .join("");
}

function toSuperscript(str) {
  return String(str)
    .split("")
    .map((ch) => SUPERSCRIPT_CHARS[ch] || ch)
    .join("");
}

function getMaxBondsForElement(el) {
  return Object.prototype.hasOwnProperty.call(MAX_COVALENT_BONDS, el)
    ? MAX_COVALENT_BONDS[el]
    : 4;
}

function getAtomBondOrderSum(atomId) {
  let sum = 0;
  for (const b of bonds) {
    if (b.a1 === atomId || b.a2 === atomId) {
      sum += b.order || 1;
    }
  }
  return sum;
}

function getFallbackNeutralHydrogens(atom) {
  if (!atom || atom.el === "H") return 0;
  const el = atom.el;
  const bondOrderSum = getAtomBondOrderSum(atom.id);

  if (!Object.prototype.hasOwnProperty.call(NEUTRAL_VALENCE, el)) {
    return 0;
  }

  let baseVal = NEUTRAL_VALENCE[el];
  if (el === "P" || el === "As" || el === "Sb") {
    if (bondOrderSum > 3) baseVal = 5;
  } else if (el === "S" || el === "Se" || el === "Te") {
    if (bondOrderSum > 4) baseVal = 6;
    else if (bondOrderSum > 2) baseVal = 4;
  } else if (el === "Cl" || el === "Br" || el === "I") {
    if (bondOrderSum > 5) baseVal = 7;
    else if (bondOrderSum > 3) baseVal = 5;
    else if (bondOrderSum > 1) baseVal = 3;
  }

  return Math.max(0, baseVal - bondOrderSum);
}

// === 透過 OpenChemLib API 計算中性基準隱含氫原子，並依正負電荷同步增減 ===
function syncAllImplicitHydrogens() {
  if (atoms.length === 0) return;

  let oclNeutralHMap = null;
  if (typeof OCL !== "undefined") {
    try {
      const neutralAtoms = atoms.map((a) => ({ ...a, charge: 0 }));
      const neutralMolfile = buildMolfileForSubset(neutralAtoms, bonds, "NeutralRef");
      if (neutralMolfile) {
        const mol = OCL.Molecule.fromMolfile(neutralMolfile);
        mol.ensureHelperArrays(7);
        oclNeutralHMap = new Map();
        atoms.forEach((a, idx) => {
          if (idx < mol.getAllAtoms()) {
            oclNeutralHMap.set(a.id, a.el === "H" ? 0 : mol.getImplicitHydrogens(idx));
          }
        });
      }
    } catch (e) {
      oclNeutralHMap = null;
    }
  }

  atoms.forEach((atom) => {
    if (atom.el === "H") {
      atom.implicitH = 0;
      return;
    }
    const neutralH =
      oclNeutralHMap && oclNeutralHMap.has(atom.id)
        ? oclNeutralHMap.get(atom.id)
        : getFallbackNeutralHydrogens(atom);
    const charge = atom.charge || 0;
    // 添加正電荷 (+) 時氫原子數同步增加；添加負電荷 (-) 時氫原子數同步減少（最低減至 0）
    atom.implicitH = Math.max(0, neutralH + charge);
  });
}

function getImplicitHydrogens(atom) {
  if (!atom || atom.el === "H") return 0;
  if (typeof atom.implicitH === "number") {
    return Math.max(0, atom.implicitH);
  }
  const neutralH = getFallbackNeutralHydrogens(atom);
  return Math.max(0, neutralH + (atom.charge || 0));
}

function formatChargeText(charge) {
  if (!charge) return "";
  if (charge === 1) return toSuperscript("+");
  if (charge > 1) return toSuperscript(`${charge}+`);
  if (charge === -1) return toSuperscript("-");
  return toSuperscript(`${Math.abs(charge)}-`);
}

function formatAtomDisplayLabel(atom, isExpandedHMode = false) {
  const chargeStr = formatChargeText(atom.charge || 0);
  if (isExpandedHMode || atom.el === "H") {
    return atom.el + chargeStr;
  }
  const hCount = getImplicitHydrogens(atom);
  const hPart = hCount === 0 ? "" : hCount === 1 ? "H" : `H${toSubscript(hCount)}`;
  return atom.el + hPart + chargeStr;
}

// === 深色質感置中通知彈窗 (取代原生 alert) ===
let customAlertKeyHandler = null;
let customAlertHideTimer = null;

function showAlert(message, type = "warning") {
  let overlay = document.getElementById("customAlertOverlay");
  if (!overlay) {
    overlay = document.createElement("div");
    overlay.id = "customAlertOverlay";
    overlay.className = "custom-alert-overlay hidden";
    overlay.setAttribute("role", "dialog");
    overlay.setAttribute("aria-modal", "true");
    overlay.innerHTML = `
      <div class="custom-alert-card warning" id="customAlertCard">
        <div class="custom-alert-icon" id="customAlertIcon"></div>
        <div class="custom-alert-message" id="customAlertMessage"></div>
        <button type="button" class="custom-alert-btn" id="customAlertConfirmBtn">確定</button>
      </div>
    `;
    document.body.appendChild(overlay);
  }

  const card = document.getElementById("customAlertCard");
  const iconEl = document.getElementById("customAlertIcon");
  const msgEl = document.getElementById("customAlertMessage");
  const confirmBtn = document.getElementById("customAlertConfirmBtn");

  const validType = type === "info" ? "info" : "warning";
  card.classList.remove("warning", "info");
  card.classList.add(validType);

  if (validType === "info") {
    iconEl.innerHTML = `
      <svg width="26" height="26" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round">
        <circle cx="12" cy="12" r="10"></circle>
        <line x1="12" y1="16" x2="12" y2="12"></line>
        <line x1="12" y1="8" x2="12.01" y2="8"></line>
      </svg>
    `;
  } else {
    iconEl.innerHTML = `
      <svg width="26" height="26" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2" stroke-linecap="round" stroke-linejoin="round">
        <path d="M10.29 3.86L1.82 18a2 2 0 0 0 1.71 3h16.94a2 2 0 0 0 1.71-3L13.71 3.86a2 2 0 0 0-3.42 0z"></path>
        <line x1="12" y1="9" x2="12" y2="13"></line>
        <line x1="12" y1="17" x2="12.01" y2="17"></line>
      </svg>
    `;
  }

  msgEl.textContent = message;

  if (customAlertHideTimer) {
    clearTimeout(customAlertHideTimer);
    customAlertHideTimer = null;
  }

  function closeAlert() {
    overlay.classList.remove("visible");
    if (customAlertKeyHandler) {
      window.removeEventListener("keydown", customAlertKeyHandler, true);
      customAlertKeyHandler = null;
    }
    customAlertHideTimer = setTimeout(() => {
      overlay.classList.add("hidden");
    }, 220);
  }

  confirmBtn.onclick = closeAlert;
  overlay.onclick = (e) => {
    if (e.target === overlay) closeAlert();
  };

  if (customAlertKeyHandler) {
    window.removeEventListener("keydown", customAlertKeyHandler, true);
  }
  customAlertKeyHandler = (e) => {
    if (e.key === "Enter" || e.key === "Escape") {
      e.preventDefault();
      e.stopPropagation();
      closeAlert();
    }
  };
  window.addEventListener("keydown", customAlertKeyHandler, true);

  if (document.activeElement && typeof document.activeElement.blur === "function") {
    document.activeElement.blur();
  }

  overlay.classList.remove("hidden");
  requestAnimationFrame(() => {
    overlay.classList.add("visible");
    confirmBtn.focus();
  });
}

const PERIODIC_TABLE = [
  ["H",1,1,"nonmetal"],["He",1,18,"noble"],
  ["Li",2,1,"alkali"],["Be",2,2,"alkaline"],["B",2,13,"metalloid"],["C",2,14,"nonmetal"],["N",2,15,"nonmetal"],["O",2,16,"nonmetal"],["F",2,17,"halogen"],["Ne",2,18,"noble"],
  ["Na",3,1,"alkali"],["Mg",3,2,"alkaline"],["Al",3,13,"metal"],["Si",3,14,"metalloid"],["P",3,15,"nonmetal"],["S",3,16,"nonmetal"],["Cl",3,17,"halogen"],["Ar",3,18,"noble"],
  ["K",4,1,"alkali"],["Ca",4,2,"alkaline"],["Sc",4,3,"transition"],["Ti",4,4,"transition"],["V",4,5,"transition"],["Cr",4,6,"transition"],["Mn",4,7,"transition"],["Fe",4,8,"transition"],["Co",4,9,"transition"],["Ni",4,10,"transition"],["Cu",4,11,"transition"],["Zn",4,12,"transition"],["Ga",4,13,"metal"],["Ge",4,14,"metalloid"],["As",4,15,"metalloid"],["Se",4,16,"nonmetal"],["Br",4,17,"halogen"],["Kr",4,18,"noble"],
  ["Rb",5,1,"alkali"],["Sr",5,2,"alkaline"],["Y",5,3,"transition"],["Zr",5,4,"transition"],["Nb",5,5,"transition"],["Mo",5,6,"transition"],["Tc",5,7,"transition"],["Ru",5,8,"transition"],["Rh",5,9,"transition"],["Pd",5,10,"transition"],["Ag",5,11,"transition"],["Cd",5,12,"transition"],["In",5,13,"metal"],["Sn",5,14,"metal"],["Sb",5,15,"metalloid"],["Te",5,16,"metalloid"],["I",5,17,"halogen"],["Xe",5,18,"noble"],
  ["Cs",6,1,"alkali"],["Ba",6,2,"alkaline"],["Hf",6,4,"transition"],["Ta",6,5,"transition"],["W",6,6,"transition"],["Re",6,7,"transition"],["Os",6,8,"transition"],["Ir",6,9,"transition"],["Pt",6,10,"transition"],["Au",6,11,"transition"],["Hg",6,12,"transition"],["Tl",6,13,"metal"],["Pb",6,14,"metal"],["Bi",6,15,"metal"],["At",6,17,"halogen"],["Rn",6,18,"noble"]
];

const RING_NAMES = {
  3: "環丙烷", 4: "環丁烷", 5: "環戊烷", 6: "環己烷",
  7: "環庚烷", 8: "環辛烷", 9: "環壬烷", 10: "環癸烷",
  12: "環十二烷", 14: "環十四烷", 16: "環十六烷", 18: "環十八烷"
};

const RING_TEMPLATES = [
  {
    key: "benzene",
    name: "苯環",
    en: "Benzene",
    svg: `<svg viewBox="0 0 40 36"><polygon points="20,4 32,11 32,25 20,32 8,25 8,11" fill="none" stroke="currentColor" stroke-width="2"/><circle cx="20" cy="18" r="7.5" fill="none" stroke="currentColor" stroke-width="1.6"/></svg>`
  },
  {
    key: "naphthalene",
    name: "萘",
    en: "Naphthalene",
    svg: `<svg viewBox="0 0 56 36"><polygon points="16,5 27,11 27,25 16,31 5,25 5,11" fill="none" stroke="currentColor" stroke-width="1.8"/><polygon points="38,5 49,11 49,25 38,31 27,25 27,11" fill="none" stroke="currentColor" stroke-width="1.8"/></svg>`
  },
  {
    key: "anthracene",
    name: "蒽",
    en: "Anthracene",
    svg: `<svg viewBox="0 0 72 36"><polygon points="14,6 24,12 24,24 14,30 4,24 4,12" fill="none" stroke="currentColor" stroke-width="1.7"/><polygon points="34,6 44,12 44,24 34,30 24,24 24,12" fill="none" stroke="currentColor" stroke-width="1.7"/><polygon points="54,6 64,12 64,24 54,30 44,24 44,12" fill="none" stroke="currentColor" stroke-width="1.7"/></svg>`
  },
  {
    key: "phenanthrene",
    name: "菲",
    en: "Phenanthrene",
    svg: `<svg viewBox="0 0 60 40"><polygon points="15,17 25,22 25,33 15,38 5,33 5,22" fill="none" stroke="currentColor" stroke-width="1.7"/><polygon points="35,17 45,22 45,33 35,38 25,33 25,22" fill="none" stroke="currentColor" stroke-width="1.7"/><polygon points="15,3 25,8 25,19 15,24 5,19 5,8" fill="none" stroke="currentColor" stroke-width="1.7"/></svg>`
  },
  {
    key: "purine",
    name: "嘌呤",
    en: "Purine",
    svg: `<svg viewBox="0 0 54 36"><polygon points="17,5 28,11 28,25 17,31 6,25 6,11" fill="none" stroke="currentColor" stroke-width="1.8"/><polyline points="28,11 42,7 49,18 42,29 28,25" fill="none" stroke="currentColor" stroke-width="1.8"/><text x="4" y="13" font-size="7" font-weight="bold" fill="#2563eb">N</text><text x="4" y="28" font-size="7" font-weight="bold" fill="#2563eb">N</text><text x="40" y="9" font-size="7" font-weight="bold" fill="#2563eb">N</text><text x="40" y="33" font-size="7" font-weight="bold" fill="#2563eb">N</text></svg>`
  },
  {
    key: "pyrimidine",
    name: "嘧啶",
    en: "Pyrimidine",
    svg: `<svg viewBox="0 0 40 36"><polygon points="20,4 32,11 32,25 20,32 8,25 8,11" fill="none" stroke="currentColor" stroke-width="1.8"/><text x="17" y="8" font-size="7.5" font-weight="bold" fill="#2563eb">N</text><text x="30" y="27" font-size="7.5" font-weight="bold" fill="#2563eb">N</text></svg>`
  },
  {
    key: "pyridine",
    name: "吡啶",
    en: "Pyridine",
    svg: `<svg viewBox="0 0 40 36"><polygon points="20,4 32,11 32,25 20,32 8,25 8,11" fill="none" stroke="currentColor" stroke-width="1.8"/><circle cx="20" cy="18" r="7" fill="none" stroke="currentColor" stroke-width="1.4"/><text x="17" y="8" font-size="7.5" font-weight="bold" fill="#2563eb">N</text></svg>`
  },
  {
    key: "piperidine",
    name: "哌啶",
    en: "Piperidine",
    svg: `<svg viewBox="0 0 40 36"><polygon points="20,4 32,11 32,25 20,32 8,25 8,11" fill="none" stroke="currentColor" stroke-width="1.8"/><text x="17" y="8" font-size="7.5" font-weight="bold" fill="#2563eb">N</text></svg>`
  }
];

const SUBSTITUENT_TEMPLATES = [
  { key: "CH3", badge: "-CH₃", name: "甲基", en: "Methyl" },
  { key: "C2H5", badge: "-C₂H₅", name: "乙基", en: "Ethyl" },
  { key: "OH", badge: "-OH", name: "羥基", en: "Hydroxyl" },
  { key: "NH2", badge: "-NH₂", name: "胺基", en: "Amino" },
  { key: "COOH", badge: "-COOH", name: "羧基", en: "Carboxyl" },
  { key: "CHO", badge: "-CHO", name: "醛基", en: "Aldehyde" },
  { key: "NO2", badge: "-NO₂", name: "硝基", en: "Nitro" },
  { key: "CN", badge: "-CN", name: "氰基", en: "Cyano" },
  { key: "OCH3", badge: "-OCH₃", name: "甲氧基", en: "Methoxy" },
  { key: "Ph", badge: "-Ph", name: "苯基 (苯環)", en: "Phenyl" },
  { key: "COCH3", badge: "-Ac", name: "乙醯基", en: "Acetyl" },
  { key: "CF3", badge: "-CF₃", name: "三氟甲基", en: "Trifluoromethyl" }
];

const LOCAL_COMPOUNDS = [
  { zh: "咖啡因", en: "caffeine" },
  { zh: "阿斯匹靈", en: "aspirin" },
  { zh: "葡萄糖", en: "glucose" },
  { zh: "果糖", en: "fructose" },
  { zh: "半乳糖", en: "galactose" },
  { zh: "蔗糖", en: "sucrose" },
  { zh: "核糖", en: "ribose" },
  { zh: "去氧核糖", en: "deoxyribose" },
  { zh: "腺嘌呤", en: "adenine" },
  { zh: "鳥嘌呤", en: "guanine" },
  { zh: "胞嘧啶", en: "cytosine" },
  { zh: "胸腺嘧啶", en: "thymine" },
  { zh: "尿嘧啶", en: "uracil" },
  { zh: "嘌呤", en: "purine" },
  { zh: "嘧啶", en: "pyrimidine" },
  { zh: "吡啶", en: "pyridine" },
  { zh: "哌啶", en: "piperidine" },
  { zh: "苯", en: "benzene" },
  { zh: "甲苯", en: "toluene" },
  { zh: "苯酚", en: "phenol" },
  { zh: "苯胺", en: "aniline" },
  { zh: "萘", en: "naphthalene" },
  { zh: "蒽", en: "anthracene" },
  { zh: "菲", en: "phenanthrene" },
  { zh: "血清素", en: "serotonin" },
  { zh: "多巴胺", en: "dopamine" },
  { zh: "腎上腺素", en: "epinephrine" },
  { zh: "正腎上腺素", en: "norepinephrine" },
  { zh: "褪黑激素", en: "melatonin" },
  { zh: "乙醯膽鹼", en: "acetylcholine" },
  { zh: "組織胺", en: "histamine" },
  { zh: "膽固醇", en: "cholesterol" },
  { zh: "睾固酮", en: "testosterone" },
  { zh: "雌二醇", en: "estradiol" },
  { zh: "皮質醇", en: "cortisol" },
  { zh: "甘氨酸", en: "glycine" },
  { zh: "丙氨酸", en: "alanine" },
  { zh: "色氨酸", en: "tryptophan" },
  { zh: "苯丙氨酸", en: "phenylalanine" },
  { zh: "酪氨酸", en: "tyrosine" },
  { zh: "半胱氨酸", en: "cysteine" },
  { zh: "組氨酸", en: "histidine" },
  { zh: "脯氨酸", en: "proline" },
  { zh: "谷氨酸 / 麩胺酸", en: "glutamic acid" },
  { zh: "天冬氨酸", en: "aspartic acid" },
  { zh: "賴氨酸 / 離胺酸", en: "lysine" },
  { zh: "精氨酸", en: "arginine" },
  { zh: "維生素C / 抗壞血酸", en: "ascorbic acid" },
  { zh: "青黴素 / 盤尼西林", en: "penicillin" },
  { zh: "布洛芬", en: "ibuprofen" },
  { zh: "普拿疼 / 乙醯胺酚", en: "acetaminophen" },
  { zh: "嗎啡", en: "morphine" },
  { zh: "尼古丁", en: "nicotine" },
  { zh: "紫杉醇", en: "paclitaxel" },
  { zh: "青蒿素", en: "artemisinin" },
  { zh: "水", en: "water" },
  { zh: "甲烷", en: "methane" },
  { zh: "乙烷", en: "ethane" },
  { zh: "丙烷", en: "propane" },
  { zh: "丁烷", en: "butane" },
  { zh: "乙醇 / 酒精", en: "ethanol" },
  { zh: "甲醇", en: "methanol" },
  { zh: "乙酸 / 醋酸", en: "acetic acid" },
  { zh: "丙酮", en: "acetone" },
  { zh: "丙酮酸", en: "pyruvic acid" },
  { zh: "乳酸", en: "lactic acid" },
  { zh: "檸檬酸", en: "citric acid" },
  { zh: "薄荷醇", en: "menthol" }
];

const canvas = document.getElementById("molCanvas");
const ctx = canvas.getContext("2d");

// 手機版斷點：螢幕寬度 <= 768px
function isMobileView() {
  return window.innerWidth <= 768;
}

function closeAllModals() {
  document.getElementById("ringLibModal")?.classList.add("hidden");
  document.getElementById("subLibModal")?.classList.add("hidden");
  document.getElementById("ptModal")?.classList.add("hidden");
}

window.addEventListener("DOMContentLoaded", () => {
  init3DViewer();
  buildPeriodicTable();
  buildRingLibrary();
  buildSubstituentLibrary();
  applyResponsiveLayout();
  resizeCanvas();
  window.addEventListener("resize", applyResponsiveLayout);
  window.addEventListener("orientationchange", () => {
    setTimeout(applyResponsiveLayout, 80);
  });
  if (window.visualViewport) {
    window.visualViewport.addEventListener("resize", applyResponsiveLayout);
  }
  bindUIEvents();
  setActiveTool("move");

  const defaultSmiles = "CN1C=NC2=C1C(=O)N(C(=O)N2C)C";
  processMolecule(defaultSmiles, false);
  setTimeout(() => loadSmilesTo2D(defaultSmiles), 120);
});

function sync3DViewerSize() {
  if (!viewer3D) return;
  viewer3D.resize();
  viewer3D.zoomTo();
  viewer3D.render();
}

function applyResponsiveLayout() {
  const editorPane = document.getElementById("editorPane");
  const viewerPane = document.getElementById("viewerPane");
  const toggleBtn = document.getElementById("toggle3DBtn");

  if (isMobileView()) {
    if (mobileActivePane === "2d") {
      editorPane.classList.remove("hidden");
      viewerPane.classList.add("hidden");
      toggleBtn.classList.remove("active");
      toggleBtn.textContent = "👁 2D / 3D";
      resizeCanvas();
      requestAnimationFrame(resizeCanvas);
    } else {
      editorPane.classList.add("hidden");
      viewerPane.classList.remove("hidden");
      toggleBtn.classList.add("active");
      toggleBtn.textContent = "← 返回 2D";
      requestAnimationFrame(() => {
        sync3DViewerSize();
        setTimeout(sync3DViewerSize, 60);
      });
    }
  } else {
    editorPane.classList.remove("hidden");
    viewerPane.classList.toggle("hidden", !desktopShow3D);
    toggleBtn.classList.toggle("active", desktopShow3D);
    toggleBtn.textContent = "👁 2D / 3D";
    resizeCanvas();
    requestAnimationFrame(() => {
      resizeCanvas();
      if (viewer3D && desktopShow3D) {
        viewer3D.resize();
        viewer3D.render();
      }
    });
  }
}

function setActiveTool(mode) {
  currentMode = mode;
  closeAllModals();
  document.querySelectorAll(".dock-btn").forEach((b) => b.classList.remove("active"));
  document.getElementById("btnErase").classList.remove("active");

  if (mode === "erase") {
    document.getElementById("btnErase").classList.add("active");
  } else if (mode === "bond") {
    const btn = document.querySelector(`.dock-btn[data-tool="bond"][data-order="${currentBondOrder}"]`);
    if (btn) btn.classList.add("active");
  } else if (mode === "charge") {
    const btn = document.querySelector(`.dock-btn[data-tool="charge"][data-val="${currentChargeVal}"]`);
    if (btn) btn.classList.add("active");
  } else if (mode === "ring") {
    if (currentRingType === "polygon") {
      const btn = document.querySelector(`.dock-btn[data-tool="ring"][data-ring="polygon"]`);
      if (btn) btn.classList.add("active");
    } else {
      document.getElementById("openRingLibBtn").classList.add("active");
    }
  } else if (mode === "substituent") {
    document.getElementById("openSubLibBtn").classList.add("active");
  } else {
    const btn = document.querySelector(`.dock-btn[data-tool="${mode}"]`);
    if (btn) btn.classList.add("active");
  }

  if (mode !== "arrow") {
    hideArrowControlBar();
  }
  canvas.style.cursor = mode === "move" ? "grab" : "crosshair";
  draw();
}

function buildRingLibrary() {
  const grid = document.getElementById("ringLibGrid");
  if (!grid) return;
  RING_TEMPLATES.forEach((tpl) => {
    const item = document.createElement("button");
    item.className = "ring-lib-item";
    item.dataset.ringKey = tpl.key;
    item.innerHTML = `${tpl.svg}<div class="ring-lib-text"><strong>${tpl.name}</strong><span>${tpl.en}</span></div>`;
    item.addEventListener("click", () => {
      currentRingType = tpl.key;
      document.querySelectorAll("#ringLibGrid .ring-lib-item").forEach((el) => el.classList.remove("active"));
      item.classList.add("active");
      setActiveTool("ring");
    });
    grid.appendChild(item);
  });
}

function buildSubstituentLibrary() {
  const grid = document.getElementById("subLibGrid");
  if (!grid) return;
  SUBSTITUENT_TEMPLATES.forEach((tpl) => {
    const item = document.createElement("button");
    item.className = "ring-lib-item";
    item.dataset.subKey = tpl.key;
    item.innerHTML = `<span class="sub-badge-tag">${tpl.badge}</span><div class="ring-lib-text"><strong>${tpl.name}</strong><span>${tpl.en}</span></div>`;
    item.addEventListener("click", () => {
      currentSubstituentType = tpl.key;
      document.querySelectorAll("#subLibGrid .ring-lib-item").forEach((el) => el.classList.remove("active"));
      item.classList.add("active");
      setActiveTool("substituent");
    });
    grid.appendChild(item);
  });
}

function buildPeriodicTable() {
  const grid = document.getElementById("ptGrid");
  if (!grid) return;
  PERIODIC_TABLE.forEach(([el, row, col, cat]) => {
    const cell = document.createElement("button");
    cell.className = `pt-cell ${cat}`;
    cell.textContent = el;
    cell.style.gridRow = row;
    cell.style.gridColumn = col;
    cell.addEventListener("click", () => {
      selectAtomElement(el);
    });
    grid.appendChild(cell);
  });
}

function selectAtomElement(el) {
  currentElement = el;
  closeAllModals();
  document.querySelectorAll(".atom-btn").forEach((b) => b.classList.remove("active"));
  const existingBtn = document.querySelector(`.atom-btn[data-atom="${el}"]`);
  if (existingBtn) {
    existingBtn.classList.add("active");
    document.getElementById("openPtBtn").classList.remove("active");
    document.getElementById("openPtBtn").textContent = "•••";
  } else {
    document.getElementById("openPtBtn").textContent = el;
    document.getElementById("openPtBtn").classList.add("active");
  }

  if (currentMode !== "bond") {
    setActiveTool("atom");
  }
}

function resizeCanvas() {
  const dpr = window.devicePixelRatio || 1;
  const rect = canvas.parentElement.getBoundingClientRect();
  if (rect.width === 0 || rect.height === 0) return;
  canvas.width = Math.round(rect.width * dpr);
  canvas.height = Math.round(rect.height * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  draw();
}

function saveState() {
  history.push(JSON.stringify({ atoms, bonds, arrows }));
  if (history.length > 40) history.shift();
  redoStack = [];
}

function updateZoomBadge() {
  document.getElementById("zoomBadge").textContent = `${Math.round(zoom * 100)}%`;
}

// === 連通分子圖分析工具 ===
function getConnectedAtomIds(seedAtomId) {
  const visited = new Set([seedAtomId]);
  const queue = [seedAtomId];
  while (queue.length > 0) {
    const curr = queue.shift();
    for (const b of bonds) {
      const next = b.a1 === curr ? b.a2 : b.a2 === curr ? b.a1 : null;
      if (next !== null && !visited.has(next)) {
        visited.add(next);
        queue.push(next);
      }
    }
  }
  return visited;
}

function getAllConnectedComponents() {
  const visited = new Set();
  const components = [];
  for (const a of atoms) {
    if (!visited.has(a.id)) {
      const compIds = getConnectedAtomIds(a.id);
      compIds.forEach((id) => visited.add(id));
      const compAtoms = atoms.filter((item) => compIds.has(item.id));
      const compBonds = bonds.filter((b) => compIds.has(b.a1) && compIds.has(b.a2));
      components.push({ atoms: compAtoms, bonds: compBonds });
    }
  }
  return components;
}

function loadSmilesTo2D(smiles) {
  try {
    if (typeof OCL === "undefined") return;
    const mol = OCL.Molecule.fromSmiles(smiles);
    mol.ensureHelperArrays(7);
    const nAtoms = mol.getAllAtoms();
    const nBonds = mol.getAllBonds();

    const newAtoms = [];
    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;

    for (let i = 0; i < nAtoms; i++) {
      const x = mol.getAtomX(i) * 32;
      const y = mol.getAtomY(i) * 32;
      minX = Math.min(minX, x); maxX = Math.max(maxX, x);
      minY = Math.min(minY, y); maxY = Math.max(maxY, y);
      newAtoms.push({
        id: i + 1, x, y,
        el: mol.getAtomLabel(i) || "C",
        charge: mol.getAtomCharge(i) || 0,
        lonePairs: 0,
        implicitH: mol.getImplicitHydrogens(i) || 0
      });
    }

    let rect = canvas.parentElement.getBoundingClientRect();
    if (rect.width === 0 || rect.height === 0) {
      rect = { width: window.innerWidth, height: window.innerHeight };
    } else {
      resizeCanvas();
    }

    const molW = Math.max(1, maxX - minX);
    const molH = Math.max(1, maxY - minY);
    const safeW = Math.max(150, rect.width - (isMobileView() ? 136 : 110));
    const safeH = Math.max(170, rect.height - (isMobileView() ? 200 : 155));
    const fitScale = Math.min(1, safeW / molW, safeH / molH);

    const cx = (minX + maxX) / 2;
    const cy = (minY + maxY) / 2;
    const targetCx = rect.width / 2;
    const targetCy = rect.height / 2 + (isMobileView() ? 44 : 10);

    newAtoms.forEach((a) => {
      a.x = targetCx + (a.x - cx) * fitScale;
      a.y = targetCy + (a.y - cy) * fitScale;
    });

    const newBonds = [];
    for (let i = 0; i < nBonds; i++) {
      newBonds.push({
        a1: mol.getBondAtom(0, i) + 1,
        a2: mol.getBondAtom(1, i) + 1,
        order: mol.getBondOrder(i) || 1
      });
    }

    saveState();
    atoms = newAtoms;
    bonds = newBonds;
    arrows = [];
    selectedArrow = null;
    hideArrowControlBar();
    syncAllImplicitHydrogens();
    draw();
  } catch (e) {
    console.error("2D 解析錯誤:", e);
  }
}

function buildMolfileForSubset(atomSubset, bondSubset, title = "MolView") {
  if (!atomSubset || atomSubset.length === 0) return "";
  const lines = [
    title,
    "  Native2D",
    "",
    `${String(atomSubset.length).padStart(3)}${String(bondSubset.length).padStart(3)}  0  0  0  0  0  0  0  0999 V2000`
  ];

  const idMap = new Map();
  const chargedEntries = [];

  atomSubset.forEach((a, idx) => {
    const oneIdx = idx + 1;
    idMap.set(a.id, oneIdx);
    const x = (a.x / 32).toFixed(4).padStart(10);
    const y = (-a.y / 32).toFixed(4).padStart(10);
    const z = "0.0000".padStart(10);
    const el = a.el.padEnd(3);
    const chgCode = a.charge === 1 ? "  3" : a.charge === -1 ? "  5" : "  0";
    lines.push(`${x}${y}${z} ${el} 0${chgCode}  0  0  0  0  0  0  0  0  0  0`);
    if (a.charge && a.charge !== 0) {
      chargedEntries.push({ idx: oneIdx, charge: a.charge });
    }
  });

  bondSubset.forEach((b) => {
    const i1 = String(idMap.get(b.a1)).padStart(3);
    const i2 = String(idMap.get(b.a2)).padStart(3);
    const ord = String(b.order).padStart(3);
    lines.push(`${i1}${i2}${ord}  0  0  0  0`);
  });

  for (let i = 0; i < chargedEntries.length; i += 8) {
    const chunk = chargedEntries.slice(i, i + 8);
    const entriesStr = chunk
      .map((item) => `${String(item.idx).padStart(4)}${String(item.charge).padStart(4)}`)
      .join("");
    lines.push(`M  CHG${String(chunk.length).padStart(3)}${entriesStr}`);
  }

  lines.push("M  END");
  return lines.join("\n");
}

function exportCanvasToMolfile() {
  return buildMolfileForSubset(atoms, bonds, "MolView");
}

// === 角度空隙分配演算法 ===
function computeRepulsionAngles(occupiedAngles, count) {
  if (count <= 0) return [];
  const TWO_PI = Math.PI * 2;
  const norm = (ang) => ((ang % TWO_PI) + TWO_PI) % TWO_PI;

  if (occupiedAngles.length === 0) {
    if (count === 1) return [-Math.PI / 2];
    if (count === 2) return [Math.PI * 0.833, Math.PI * 0.167];
    if (count === 3) return [-Math.PI / 2, Math.PI / 6, (5 * Math.PI) / 6];
    const res = [];
    for (let i = 0; i < count; i++) {
      res.push(-Math.PI / 2 + (i * TWO_PI) / count);
    }
    return res;
  }

  if (occupiedAngles.length === 1) {
    const opp = occupiedAngles[0] + Math.PI;
    if (count === 1) return [opp];
    if (count === 2) return [opp - Math.PI / 3, opp + Math.PI / 3];
    if (count === 3) return [opp - Math.PI * 0.34, opp, opp + Math.PI * 0.34];
    const res = [];
    const span = Math.PI * 1.4;
    for (let i = 0; i < count; i++) {
      res.push(opp - span / 2 + (span * (i + 0.5)) / count);
    }
    return res;
  }

  const sorted = occupiedAngles.map(norm).sort((a, b) => a - b);
  const gaps = [];
  for (let i = 0; i < sorted.length; i++) {
    const start = sorted[i];
    const end = i + 1 < sorted.length ? sorted[i + 1] : sorted[0] + TWO_PI;
    const span = Math.max(0.01, end - start);
    gaps.push({ start, span, assigned: 0 });
  }

  for (let k = 0; k < count; k++) {
    let bestIdx = 0;
    let bestScore = -1;
    for (let g = 0; g < gaps.length; g++) {
      const score = gaps[g].span / (gaps[g].assigned + 1) + gaps[g].span * 0.001;
      if (score > bestScore) {
        bestScore = score;
        bestIdx = g;
      }
    }
    gaps[bestIdx].assigned += 1;
  }

  const result = [];
  for (const g of gaps) {
    if (g.assigned > 0) {
      for (let j = 0; j < g.assigned; j++) {
        result.push(g.start + (g.span * (j + 1)) / (g.assigned + 1));
      }
    }
  }
  return result;
}

function getExplicitHydrogenPositions(atom) {
  if (!showHydrogens2D || !atom || atom.el === "H") return [];
  const hCount = getImplicitHydrogens(atom);
  if (hCount <= 0) return [];

  const bondAngles = [];
  for (const b of bonds) {
    const otherId = b.a1 === atom.id ? b.a2 : b.a2 === atom.id ? b.a1 : null;
    if (otherId !== null) {
      const other = atoms.find((item) => item.id === otherId);
      if (other) {
        bondAngles.push(Math.atan2(other.y - atom.y, other.x - atom.x));
      }
    }
  }

  const hAngles = computeRepulsionAngles(bondAngles, hCount);
  const hLen = 28;
  return hAngles.map((ang) => ({
    x: atom.x + Math.cos(ang) * hLen,
    y: atom.y + Math.sin(ang) * hLen,
    angle: ang
  }));
}

function draw() {
  const rect = canvas.parentElement.getBoundingClientRect();
  if (rect.width === 0 || rect.height === 0) return;

  // 每次渲染前同步隱含氫原子數，確保結構或電荷異動時畫面即時更新
  syncAllImplicitHydrogens();

  ctx.clearRect(0, 0, rect.width, rect.height);

  ctx.save();
  ctx.translate(rect.width / 2, rect.height / 2);
  ctx.scale(zoom, zoom);
  ctx.translate(-rect.width / 2, -rect.height / 2);

  // 1. 繪製化學鍵
  bonds.forEach((b) => {
    const a1 = atoms.find((a) => a.id === b.a1);
    const a2 = atoms.find((a) => a.id === b.a2);
    if (!a1 || !a2) return;

    const isHover = hoverBond === b;
    ctx.strokeStyle = isHover ? "#0284c7" : "#1e293b";
    ctx.lineWidth = isHover ? 3 : 2;
    ctx.lineCap = "round";

    const dx = a2.x - a1.x;
    const dy = a2.y - a1.y;
    const len = Math.hypot(dx, dy) || 1;
    const nx = -dy / len;
    const ny = dx / len;

    if (b.order === 1) {
      drawLine(a1.x, a1.y, a2.x, a2.y);
    } else if (b.order === 2) {
      const off = 3.2;
      drawLine(a1.x + nx * off, a1.y + ny * off, a2.x + nx * off, a2.y + ny * off);
      drawLine(a1.x - nx * off, a1.y - ny * off, a2.x - nx * off, a2.y - ny * off);
    } else if (b.order === 3) {
      const off = 4.5;
      drawLine(a1.x, a1.y, a2.x, a2.y);
      drawLine(a1.x + nx * off, a1.y + ny * off, a2.x + nx * off, a2.y + ny * off);
      drawLine(a1.x - nx * off, a1.y - ny * off, a2.x - nx * off, a2.y - ny * off);
    }
  });

  // 1b. 若開啟「顯示 2D 氫原子」，繪製 C-H / X-H 鍵結與 H 標籤
  const cachedHPositions = new Map();
  if (showHydrogens2D) {
    atoms.forEach((a) => {
      const hList = getExplicitHydrogenPositions(a);
      cachedHPositions.set(a.id, hList);
      hList.forEach((hp) => {
        ctx.strokeStyle = "#64748b";
        ctx.lineWidth = 1.6;
        ctx.lineCap = "round";
        drawLine(a.x, a.y, hp.x, hp.y);

        ctx.fillStyle = "#ffffff";
        ctx.beginPath();
        ctx.arc(hp.x, hp.y, 7.5, 0, Math.PI * 2);
        ctx.fill();

        ctx.fillStyle = ATOM_COLORS.H;
        ctx.font = "bold 12px system-ui, sans-serif";
        ctx.textAlign = "center";
        ctx.textBaseline = "middle";
        ctx.fillText("H", hp.x, hp.y);
      });
    });
  }

  // 2. 拖曳鍵結預覽
  if (dragStartAtom && dragPos) {
    ctx.strokeStyle = "#38bdf8";
    ctx.lineWidth = 2;
    ctx.setLineDash([4, 4]);
    drawLine(dragStartAtom.x, dragStartAtom.y, dragPos.x, dragPos.y);
    ctx.setLineDash([]);
  }

  // 3. 拖曳多邊形環預覽 (3~18 環)
  if (dragRingStart && currentRingType === "polygon") {
    const preview = buildPolygonVertices(dragRingStart, dragRingSides, dragRingAngle, dragRingAttachAtom);
    ctx.save();
    ctx.strokeStyle = "#0284c7";
    ctx.fillStyle = "rgba(14, 165, 233, 0.10)";
    ctx.lineWidth = 2;
    ctx.setLineDash([5, 4]);
    ctx.beginPath();
    preview.forEach((pt, idx) => {
      if (idx === 0) ctx.moveTo(pt.x, pt.y);
      else ctx.lineTo(pt.x, pt.y);
    });
    ctx.closePath();
    ctx.fill();
    ctx.stroke();
    ctx.setLineDash([]);

    const cx = preview.reduce((s, p) => s + p.x, 0) / preview.length;
    const cy = preview.reduce((s, p) => s + p.y, 0) / preview.length;
    const label = RING_NAMES[dragRingSides]
      ? `${dragRingSides} 員環 (${RING_NAMES[dragRingSides]})`
      : `${dragRingSides} 員環`;
    ctx.font = "bold 12px system-ui, sans-serif";
    const tw = ctx.measureText(label).width + 14;
    ctx.fillStyle = "rgba(15, 23, 42, 0.88)";
    ctx.beginPath();
    ctx.roundRect(cx - tw / 2, cy - 12, tw, 24, 6);
    ctx.fill();
    ctx.fillStyle = "#38bdf8";
    ctx.textAlign = "center";
    ctx.textBaseline = "middle";
    ctx.fillText(label, cx, cy);
    ctx.restore();
  }

  // 4. 芳香/生醫環模板懸浮預覽
  if (currentMode === "ring" && currentRingType !== "polygon" && hoverPos && !dragRingStart) {
    const anchor = hoverAtom ? { x: hoverAtom.x, y: hoverAtom.y } : hoverPos;
    const tpl = getRingTemplateGeometry(currentRingType, anchor, hoverAtom);
    if (tpl) {
      ctx.save();
      ctx.strokeStyle = "rgba(2, 132, 199, 0.55)";
      ctx.lineWidth = 1.8;
      ctx.setLineDash([4, 3]);
      tpl.bonds.forEach((b) => {
        const p1 = tpl.atoms[b.a1];
        const p2 = tpl.atoms[b.a2];
        if (!p1 || !p2) return;
        drawLine(p1.x, p1.y, p2.x, p2.y);
      });
      ctx.setLineDash([]);
      tpl.atoms.forEach((a) => {
        if (a.el !== "C") {
          ctx.fillStyle = "#2563eb";
          ctx.font = "bold 12px system-ui, sans-serif";
          ctx.textAlign = "center";
          ctx.textBaseline = "middle";
          ctx.fillText(a.el, a.x, a.y);
        }
      });
      ctx.restore();
    }
  }

  // 4b. 常見取代基懸浮預覽
  if (currentMode === "substituent" && hoverPos) {
    const anchor = hoverAtom ? { x: hoverAtom.x, y: hoverAtom.y } : hoverPos;
    const subGeo = getSubstituentGeometry(currentSubstituentType, anchor, hoverAtom);
    if (subGeo) {
      ctx.save();
      ctx.strokeStyle = "rgba(2, 132, 199, 0.65)";
      ctx.lineWidth = 2;
      ctx.setLineDash([4, 3]);
      subGeo.bonds.forEach((b) => {
        const p1 = b.fromRoot ? anchor : subGeo.atoms[b.a1];
        const p2 = subGeo.atoms[b.a2];
        if (!p1 || !p2) return;
        const dx = p2.x - p1.x;
        const dy = p2.y - p1.y;
        const len = Math.hypot(dx, dy) || 1;
        const nx = -dy / len;
        const ny = dx / len;
        if (b.order === 2) {
          drawLine(p1.x + nx * 2.8, p1.y + ny * 2.8, p2.x + nx * 2.8, p2.y + ny * 2.8);
          drawLine(p1.x - nx * 2.8, p1.y - ny * 2.8, p2.x - nx * 2.8, p2.y - ny * 2.8);
        } else if (b.order === 3) {
          drawLine(p1.x, p1.y, p2.x, p2.y);
          drawLine(p1.x + nx * 4, p1.y + ny * 4, p2.x + nx * 4, p2.y + ny * 4);
          drawLine(p1.x - nx * 4, p1.y - ny * 4, p2.x - nx * 4, p2.y - ny * 4);
        } else {
          drawLine(p1.x, p1.y, p2.x, p2.y);
        }
      });
      ctx.setLineDash([]);
      subGeo.atoms.forEach((a) => {
        if (a.el !== "C") {
          ctx.fillStyle = ATOM_COLORS[a.el] || "#0284c7";
          ctx.font = "bold 12px system-ui, sans-serif";
          ctx.textAlign = "center";
          ctx.textBaseline = "middle";
          ctx.fillText(a.el + formatChargeText(a.charge || 0), a.x, a.y);
        }
      });
      ctx.restore();
    }
  }

  // 5. 繪製原子節點（含隱含氫原子數與電荷標示）
  atoms.forEach((a) => {
    const degree = bonds.filter((b) => b.a1 === a.id || b.a2 === a.id).length;
    const drawnHs = cachedHPositions.get(a.id) || [];
    const showLabel =
      a.el !== "C" ||
      degree === 0 ||
      (a.charge || 0) !== 0 ||
      (a.lonePairs && a.lonePairs > 0) ||
      (showHydrogens2D && drawnHs.length > 0);

    if (hoverAtom === a) {
      ctx.fillStyle = "rgba(186, 230, 253, 0.75)";
      ctx.beginPath();
      ctx.arc(a.x, a.y, 15, 0, Math.PI * 2);
      ctx.fill();
    }

    if (showLabel) {
      const fullText = formatAtomDisplayLabel(a, showHydrogens2D);
      ctx.font = "bold 14px system-ui, sans-serif";
      const textW = ctx.measureText(fullText).width;
      const maskR = Math.max(10, textW / 2 + 3.5);

      ctx.fillStyle = "#ffffff";
      ctx.beginPath();
      ctx.arc(a.x, a.y, maskR, 0, Math.PI * 2);
      ctx.fill();

      ctx.fillStyle = ATOM_COLORS[a.el] || "#1e293b";
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(fullText, a.x, a.y);
    }

    if (a.lonePairs && a.lonePairs > 0) {
      drawLonePairs(a, drawnHs);
    }
  });

  // 6. 繪製電子轉移彎箭頭
  arrows.forEach((arr) => {
    const isSel = selectedArrow === arr;
    const isHov = hoverArrow === arr;
    drawCurvedArrow(arr, isSel || isHov, isSel);
  });
  if (dragArrowStart && dragPos) {
    drawCurvedArrow({ x1: dragArrowStart.x, y1: dragArrowStart.y, x2: dragPos.x, y2: dragPos.y, curve: 0.35 }, true, false);
  }

  ctx.restore();
}

function drawLonePairs(atom, drawnHs = []) {
  const count = Math.min(4, atom.lonePairs || 0);
  if (count <= 0) return;

  const occupiedAngles = [];
  for (const b of bonds) {
    const otherId = b.a1 === atom.id ? b.a2 : b.a2 === atom.id ? b.a1 : null;
    if (otherId !== null) {
      const other = atoms.find((item) => item.id === otherId);
      if (other) {
        occupiedAngles.push(Math.atan2(other.y - atom.y, other.x - atom.x));
      }
    }
  }
  for (const hp of drawnHs) {
    occupiedAngles.push(hp.angle);
  }

  const lpAngles = computeRepulsionAngles(occupiedAngles, count);
  const fullLabel = formatAtomDisplayLabel(atom, showHydrogens2D);
  const dist = fullLabel.length >= 3 ? 17 : 13.5;

  ctx.fillStyle = "#0f172a";
  for (const ang of lpAngles) {
    const cx = atom.x + Math.cos(ang) * dist;
    const cy = atom.y + Math.sin(ang) * dist;
    const tx = -Math.sin(ang) * 2.6;
    const ty = Math.cos(ang) * 2.6;

    ctx.beginPath();
    ctx.arc(cx - tx, cy - ty, 1.85, 0, Math.PI * 2);
    ctx.arc(cx + tx, cy + ty, 1.85, 0, Math.PI * 2);
    ctx.fill();
  }
}

function getArrowControlPoint(arr) {
  const dx = arr.x2 - arr.x1;
  const dy = arr.y2 - arr.y1;
  const dist = Math.hypot(dx, dy) || 1;
  const mx = (arr.x1 + arr.x2) / 2;
  const my = (arr.y1 + arr.y2) / 2;
  const nx = -dy / dist;
  const ny = dx / dist;
  const curveVal = typeof arr.curve === "number" ? arr.curve : 0.35;
  const curveHeight = curveVal * dist;
  return {
    cx: mx + nx * curveHeight,
    cy: my + ny * curveHeight
  };
}

function drawCurvedArrow(arr, highlight = false, showHandle = false) {
  const { x1, y1, x2, y2 } = arr;
  const dist = Math.hypot(x2 - x1, y2 - y1);
  if (dist < 8) return;

  const { cx, cy } = getArrowControlPoint(arr);

  ctx.strokeStyle = highlight ? "#0284c7" : "#e11d48";
  ctx.fillStyle = highlight ? "#0284c7" : "#e11d48";
  ctx.lineWidth = highlight ? 2.2 : 1.8;

  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.quadraticCurveTo(cx, cy, x2, y2);
  ctx.stroke();

  const angle = Math.atan2(y2 - cy, x2 - cx);
  const headLen = 8.5;
  ctx.beginPath();
  ctx.moveTo(x2, y2);
  ctx.lineTo(x2 - headLen * Math.cos(angle - Math.PI / 6), y2 - headLen * Math.sin(angle - Math.PI / 6));
  ctx.lineTo(x2 - headLen * Math.cos(angle + Math.PI / 6), y2 - headLen * Math.sin(angle + Math.PI / 6));
  ctx.closePath();
  ctx.fill();

  if (showHandle) {
    const midX = 0.25 * x1 + 0.5 * cx + 0.25 * x2;
    const midY = 0.25 * y1 + 0.5 * cy + 0.25 * y2;
    ctx.fillStyle = "#ffffff";
    ctx.strokeStyle = "#0284c7";
    ctx.lineWidth = 2;
    ctx.beginPath();
    ctx.arc(midX, midY, 5, 0, Math.PI * 2);
    ctx.fill();
    ctx.stroke();
  }
}

function drawLine(x1, y1, x2, y2) {
  ctx.beginPath();
  ctx.moveTo(x1, y1);
  ctx.lineTo(x2, y2);
  ctx.stroke();
}

function getMousePos(e) {
  const rect = canvas.getBoundingClientRect();
  const rawX = e.clientX - rect.left;
  const rawY = e.clientY - rect.top;
  return {
    x: (rawX - rect.width / 2) / zoom + rect.width / 2,
    y: (rawY - rect.height / 2) / zoom + rect.height / 2
  };
}

function findAtomAt(pos) {
  return atoms.find((a) => Math.hypot(a.x - pos.x, a.y - pos.y) < 16) || null;
}

function findBondAt(pos) {
  return bonds.find((b) => {
    const a1 = atoms.find((a) => a.id === b.a1);
    const a2 = atoms.find((a) => a.id === b.a2);
    if (!a1 || !a2) return false;
    return pointToSegDist(pos.x, pos.y, a1.x, a1.y, a2.x, a2.y) < 8;
  }) || null;
}

function findArrowAt(pos) {
  return arrows.find((arr) => {
    const { cx, cy } = getArrowControlPoint(arr);
    for (let t = 0; t <= 1.01; t += 0.1) {
      const bx = (1 - t) * (1 - t) * arr.x1 + 2 * (1 - t) * t * cx + t * t * arr.x2;
      const by = (1 - t) * (1 - t) * arr.y1 + 2 * (1 - t) * t * cy + t * t * arr.y2;
      if (Math.hypot(pos.x - bx, pos.y - by) < 14) return true;
    }
    return false;
  }) || null;
}

function isNearArrowHandle(pos, arr) {
  if (!arr) return false;
  const { cx, cy } = getArrowControlPoint(arr);
  const midX = 0.25 * arr.x1 + 0.5 * cx + 0.25 * arr.x2;
  const midY = 0.25 * arr.y1 + 0.5 * cy + 0.25 * arr.y2;
  return Math.hypot(pos.x - midX, pos.y - midY) < 14;
}

function pointToSegDist(px, py, x1, y1, x2, y2) {
  const l2 = (x2 - x1) ** 2 + (y2 - y1) ** 2;
  if (l2 === 0) return Math.hypot(px - x1, py - y1);
  let t = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / l2;
  t = Math.max(0, Math.min(1, t));
  return Math.hypot(px - (x1 + t * (x2 - x1)), py - (y1 + t * (y2 - y1)));
}

function showArrowControlBar(arr) {
  selectedArrow = arr;
  const bar = document.getElementById("arrowControlBar");
  if (bar) bar.classList.remove("hidden");
  draw();
}

function hideArrowControlBar() {
  selectedArrow = null;
  const bar = document.getElementById("arrowControlBar");
  if (bar) bar.classList.add("hidden");
}

function eraseAtPoint(pos) {
  let erased = false;
  const hitAtom = findAtomAt(pos);
  if (hitAtom) {
    if (!eraseHasSavedState) {
      saveState();
      eraseHasSavedState = true;
    }
    atoms = atoms.filter((a) => a.id !== hitAtom.id);
    bonds = bonds.filter((b) => b.a1 !== hitAtom.id && b.a2 !== hitAtom.id);
    if (hoverAtom === hitAtom) hoverAtom = null;
    erased = true;
  }

  const hitBond = findBondAt(pos);
  if (hitBond) {
    if (!eraseHasSavedState) {
      saveState();
      eraseHasSavedState = true;
    }
    bonds = bonds.filter((b) => b !== hitBond);
    if (hoverBond === hitBond) hoverBond = null;
    erased = true;
  }

  const hitArrow = findArrowAt(pos);
  if (hitArrow) {
    if (!eraseHasSavedState) {
      saveState();
      eraseHasSavedState = true;
    }
    if (selectedArrow === hitArrow) hideArrowControlBar();
    arrows = arrows.filter((arr) => arr !== hitArrow);
    if (hoverArrow === hitArrow) hoverArrow = null;
    erased = true;
  }

  return erased;
}

// === 滑鼠滾輪縮放整個畫布 ===
canvas.addEventListener("wheel", (e) => {
  e.preventDefault();
  const factor = e.deltaY < 0 ? 1.08 : 1 / 1.08;
  zoom = Math.max(0.3, Math.min(3.0, zoom * factor));
  updateZoomBadge();
  draw();
}, { passive: false });

canvas.addEventListener("contextmenu", (e) => e.preventDefault());

canvas.addEventListener("mousemove", (e) => {
  const pos = getMousePos(e);
  hoverPos = pos;

  if (isRightRotating) {
    const currentAngle = Math.atan2(pos.y - rotateCenter.y, pos.x - rotateCenter.x);
    const deltaAngle = currentAngle - lastRotateAngle;
    lastRotateAngle = currentAngle;

    const cos = Math.cos(deltaAngle);
    const sin = Math.sin(deltaAngle);

    atoms.forEach((a) => {
      const dx = a.x - rotateCenter.x;
      const dy = a.y - rotateCenter.y;
      a.x = rotateCenter.x + dx * cos - dy * sin;
      a.y = rotateCenter.y + dx * sin + dy * cos;
    });

    arrows.forEach((arr) => {
      const dx1 = arr.x1 - rotateCenter.x;
      const dy1 = arr.y1 - rotateCenter.y;
      arr.x1 = rotateCenter.x + dx1 * cos - dy1 * sin;
      arr.y1 = rotateCenter.y + dx1 * sin + dy1 * cos;

      const dx2 = arr.x2 - rotateCenter.x;
      const dy2 = arr.y2 - rotateCenter.y;
      arr.x2 = rotateCenter.x + dx2 * cos - dy2 * sin;
      arr.y2 = rotateCenter.y + dx2 * sin + dy2 * cos;
    });

    const currentDist = Math.hypot(e.clientX - rotateScreenCenter.x, e.clientY - rotateScreenCenter.y);
    if (lastRightDist > 18 && currentDist > 18) {
      const scaleRatio = currentDist / lastRightDist;
      zoom = Math.max(0.3, Math.min(3.0, zoom * scaleRatio));
      updateZoomBadge();
    }
    lastRightDist = currentDist;

    draw();
    return;
  }

  if (isErasingDrag && currentMode === "erase") {
    let anyErased = false;
    if (lastErasePos) {
      const dist = Math.hypot(pos.x - lastErasePos.x, pos.y - lastErasePos.y);
      const steps = Math.max(1, Math.ceil(dist / 6));
      for (let s = 1; s <= steps; s++) {
        const t = s / steps;
        const sample = {
          x: lastErasePos.x + (pos.x - lastErasePos.x) * t,
          y: lastErasePos.y + (pos.y - lastErasePos.y) * t
        };
        if (eraseAtPoint(sample)) anyErased = true;
      }
    } else {
      anyErased = eraseAtPoint(pos);
    }
    lastErasePos = pos;
    hoverAtom = findAtomAt(pos);
    hoverBond = hoverAtom ? null : findBondAt(pos);
    hoverArrow = (!hoverAtom && !hoverBond) ? findArrowAt(pos) : null;
    if (anyErased) draw();
    return;
  }

  if (dragMoveLast) {
    const dx = pos.x - dragMoveLast.x;
    const dy = pos.y - dragMoveLast.y;
    dragMoveLast = pos;
    if (dragMoveAtomIds) {
      atoms.forEach((a) => {
        if (dragMoveAtomIds.has(a.id)) {
          a.x += dx;
          a.y += dy;
        }
      });
    } else {
      atoms.forEach((a) => { a.x += dx; a.y += dy; });
      arrows.forEach((arr) => { arr.x1 += dx; arr.y1 += dy; arr.x2 += dx; arr.y2 += dy; });
    }
    draw();
    return;
  }

  if (dragArrowCurve && selectedArrow) {
    const dx = selectedArrow.x2 - selectedArrow.x1;
    const dy = selectedArrow.y2 - selectedArrow.y1;
    const dist = Math.hypot(dx, dy) || 1;
    const mx = (selectedArrow.x1 + selectedArrow.x2) / 2;
    const my = (selectedArrow.y1 + selectedArrow.y2) / 2;
    const nx = -dy / dist;
    const ny = dx / dist;
    const proj = ((pos.x - mx) * nx + (pos.y - my) * ny) * 2;
    selectedArrow.curve = Math.max(-0.95, Math.min(0.95, proj / dist));
    draw();
    return;
  }

  if (dragRingStart && currentRingType === "polygon") {
    const dx = pos.x - dragRingStart.x;
    const dy = pos.y - dragRingStart.y;
    const screenDist = Math.hypot(dx, dy) * zoom;
    if (screenDist < 14) {
      dragRingSides = 6;
      dragRingAngle = -Math.PI / 2;
    } else {
      dragRingSides = Math.min(18, Math.max(3, Math.floor((screenDist - 14) / 14) + 3));
      dragRingAngle = Math.atan2(dy, dx);
    }
    dragPos = pos;
    draw();
    return;
  }

  hoverAtom = findAtomAt(pos);
  hoverBond = hoverAtom ? null : findBondAt(pos);
  hoverArrow = (!hoverAtom && !hoverBond) ? findArrowAt(pos) : null;

  if (dragStartAtom) {
    const dx = pos.x - dragStartAtom.x;
    const dy = pos.y - dragStartAtom.y;
    const angle = Math.round(Math.atan2(dy, dx) / (Math.PI / 6)) * (Math.PI / 6);
    const dist = Math.hypot(dx, dy) < 20 ? 36 : Math.hypot(dx, dy);
    dragPos = {
      x: dragStartAtom.x + Math.cos(angle) * dist,
      y: dragStartAtom.y + Math.sin(angle) * dist
    };
  } else if (dragArrowStart) {
    dragPos = pos;
  }
  draw();
});

canvas.addEventListener("mousedown", (e) => {
  closeAllModals();
  const pos = getMousePos(e);

  if (e.button === 2) {
    if (atoms.length === 0) return;
    saveState();
    isRightRotating = true;
    rotateCenter = {
      x: atoms.reduce((sum, a) => sum + a.x, 0) / atoms.length,
      y: atoms.reduce((sum, a) => sum + a.y, 0) / atoms.length
    };
    const rect = canvas.getBoundingClientRect();
    rotateScreenCenter = {
      x: rect.left + rect.width / 2 + (rotateCenter.x - rect.width / 2) * zoom,
      y: rect.top + rect.height / 2 + (rotateCenter.y - rect.height / 2) * zoom
    };
    lastRotateAngle = Math.atan2(pos.y - rotateCenter.y, pos.x - rotateCenter.x);
    lastRightDist = Math.hypot(e.clientX - rotateScreenCenter.x, e.clientY - rotateScreenCenter.y);
    canvas.style.cursor = "grabbing";
    return;
  }

  if (selectedArrow && isNearArrowHandle(pos, selectedArrow)) {
    saveState();
    dragArrowCurve = true;
    return;
  }

  const hitAtom = findAtomAt(pos);
  const hitBond = hitAtom ? null : findBondAt(pos);
  const hitArrow = (!hitAtom && !hitBond) ? findArrowAt(pos) : null;

  if (currentMode === "move") {
    if (hitArrow) {
      showArrowControlBar(hitArrow);
      return;
    }
    if (hitAtom || hitBond) {
      const seedId = hitAtom ? hitAtom.id : hitBond.a1;
      saveState();
      dragMoveAtomIds = getConnectedAtomIds(seedId);
      dragMoveLast = pos;
      canvas.style.cursor = "grabbing";
      return;
    }
    if (atoms.length > 0 || arrows.length > 0) {
      saveState();
      dragMoveAtomIds = null;
      dragMoveLast = pos;
      canvas.style.cursor = "grabbing";
    }
    return;
  }

  if (currentMode === "erase") {
    isErasingDrag = true;
    eraseHasSavedState = false;
    lastErasePos = pos;
    if (eraseAtPoint(pos)) {
      draw();
    }
    return;
  }

  if (currentMode === "atom") {
    if (hitAtom && hitAtom.el === currentElement) return;
    saveState();
    if (hitAtom) {
      hitAtom.el = currentElement;
      const maxNeg = -getMaxBondsForElement(currentElement);
      if (hitAtom.charge < maxNeg) hitAtom.charge = maxNeg;
    } else {
      atoms.push({
        id: Date.now() + Math.random(),
        x: pos.x,
        y: pos.y,
        el: currentElement,
        charge: 0,
        lonePairs: 0,
        implicitH: 0
      });
    }
    syncAllImplicitHydrogens();
    draw();
    return;
  }

  if (currentMode === "lonepair" && hitAtom) {
    saveState();
    hitAtom.lonePairs = ((hitAtom.lonePairs || 0) + 1) % 5;
    draw();
    return;
  }

  if (currentMode === "arrow") {
    if (hitArrow) {
      showArrowControlBar(hitArrow);
      return;
    }
    dragArrowStart = hitAtom ? { x: hitAtom.x, y: hitAtom.y } : pos;
    dragPos = pos;
    draw();
    return;
  }

  // 電荷變更事件：添加正電荷 (+) 同步增加隱含氫原子數；添加負電荷 (-) 同步減少隱含氫原子數（最低減至 0）
  if (currentMode === "charge" && hitAtom) {
    const currCharge = hitAtom.charge || 0;
    if (currentChargeVal > 0) {
      if (currCharge >= 10) return;
      saveState();
      hitAtom.charge = currCharge + 1;
    } else {
      const maxBonds = getMaxBondsForElement(hitAtom.el);
      const minCharge = -maxBonds;
      if (currCharge <= minCharge) return;
      saveState();
      hitAtom.charge = currCharge - 1;
    }
    syncAllImplicitHydrogens();
    draw();
    return;
  }

  if (currentMode === "ring") {
    if (currentRingType === "polygon") {
      dragRingStart = hitAtom ? { x: hitAtom.x, y: hitAtom.y } : pos;
      dragRingAttachAtom = hitAtom;
      dragRingSides = 6;
      dragRingAngle = -Math.PI / 2;
      dragPos = pos;
      draw();
    } else {
      saveState();
      placeRingTemplate(currentRingType, hitAtom ? { x: hitAtom.x, y: hitAtom.y } : pos, hitAtom);
      syncAllImplicitHydrogens();
      draw();
    }
    return;
  }

  if (currentMode === "substituent") {
    saveState();
    placeSubstituent(currentSubstituentType, hitAtom ? { x: hitAtom.x, y: hitAtom.y } : pos, hitAtom);
    syncAllImplicitHydrogens();
    draw();
    return;
  }

  if (currentMode === "bond") {
    if (hitBond) {
      saveState();
      hitBond.order = hitBond.order >= 3 ? 1 : hitBond.order + 1;
      syncAllImplicitHydrogens();
      draw();
      return;
    }
    if (hitAtom) {
      dragStartAtom = hitAtom;
      dragPos = pos;
    } else {
      saveState();
      const newId = Date.now() + Math.random();
      const newAtom = { id: newId, x: pos.x, y: pos.y, el: currentElement, charge: 0, lonePairs: 0, implicitH: 0 };
      atoms.push(newAtom);
      syncAllImplicitHydrogens();
      dragStartAtom = newAtom;
      dragPos = pos;
      draw();
    }
  }
});

window.addEventListener("mouseup", (e) => {
  if (isErasingDrag) {
    isErasingDrag = false;
    eraseHasSavedState = false;
    lastErasePos = null;
  }

  if (e.button === 2 && isRightRotating) {
    isRightRotating = false;
    canvas.style.cursor = currentMode === "move" ? "grab" : "crosshair";
    return;
  }

  if (dragMoveLast) {
    dragMoveLast = null;
    dragMoveAtomIds = null;
    canvas.style.cursor = "grab";
    return;
  }

  if (dragArrowCurve) {
    dragArrowCurve = false;
    draw();
    return;
  }

  if (dragRingStart && currentRingType === "polygon") {
    saveState();
    commitPolygonRing(dragRingStart, dragRingSides, dragRingAngle, dragRingAttachAtom);
    dragRingStart = null;
    dragRingAttachAtom = null;
    dragPos = null;
    syncAllImplicitHydrogens();
    draw();
    return;
  }

  if (dragArrowStart) {
    const pos = dragPos || getMousePos(e);
    const targetAtom = findAtomAt(pos);
    const endPos = targetAtom ? { x: targetAtom.x, y: targetAtom.y } : pos;
    if (Math.hypot(endPos.x - dragArrowStart.x, endPos.y - dragArrowStart.y) > 12) {
      saveState();
      const newArr = {
        x1: dragArrowStart.x,
        y1: dragArrowStart.y,
        x2: endPos.x,
        y2: endPos.y,
        curve: 0.35
      };
      arrows.push(newArr);
      showArrowControlBar(newArr);
    }
    dragArrowStart = null;
    dragPos = null;
    draw();
    return;
  }

  if (!dragStartAtom) return;
  const pos = dragPos || getMousePos(e);
  const targetAtom = findAtomAt(pos);

  if (targetAtom && targetAtom !== dragStartAtom) {
    saveState();
    const exists = bonds.find(
      (b) => (b.a1 === dragStartAtom.id && b.a2 === targetAtom.id) || (b.a1 === targetAtom.id && b.a2 === dragStartAtom.id)
    );
    if (exists) {
      exists.order = currentBondOrder;
    } else {
      bonds.push({ a1: dragStartAtom.id, a2: targetAtom.id, order: currentBondOrder });
    }
  } else if (Math.hypot(pos.x - dragStartAtom.x, pos.y - dragStartAtom.y) > 12) {
    saveState();
    const newId = Date.now() + Math.random();
    atoms.push({ id: newId, x: pos.x, y: pos.y, el: currentElement, charge: 0, lonePairs: 0, implicitH: 0 });
    bonds.push({ a1: dragStartAtom.id, a2: newId, order: currentBondOrder });
  } else if (dragStartAtom.el !== currentElement) {
    saveState();
    dragStartAtom.el = currentElement;
  }

  dragStartAtom = null;
  dragPos = null;
  syncAllImplicitHydrogens();
  draw();
});

// === 手機觸控支援 ===
canvas.addEventListener("touchstart", (e) => {
  e.preventDefault();
  if (e.touches.length >= 2) {
    if (!isTwoFingerGesture && preTouchSnapshot) {
      const snap = JSON.parse(preTouchSnapshot);
      atoms = snap.atoms;
      bonds = snap.bonds;
      arrows = snap.arrows || [];
      if (history.length > 0) history.pop();
    }
    preTouchSnapshot = null;
    isTwoFingerGesture = true;
    isErasingDrag = false;
    eraseHasSavedState = false;
    lastErasePos = null;
    dragStartAtom = null;
    dragArrowStart = null;
    dragArrowCurve = false;
    dragRingStart = null;
    dragMoveLast = null;
    dragMoveAtomIds = null;
    dragPos = null;

    if (atoms.length > 0) {
      saveState();
      rotateCenter = {
        x: atoms.reduce((sum, a) => sum + a.x, 0) / atoms.length,
        y: atoms.reduce((sum, a) => sum + a.y, 0) / atoms.length
      };
    }

    const t1 = e.touches[0];
    const t2 = e.touches[1];
    lastTouchAngle = Math.atan2(t2.clientY - t1.clientY, t2.clientX - t1.clientX);
    lastTouchDist = Math.hypot(t2.clientX - t1.clientX, t2.clientY - t1.clientY);
    draw();
    return;
  }

  if (e.touches.length === 1 && !isTwoFingerGesture) {
    preTouchSnapshot = JSON.stringify({ atoms, bonds, arrows });
    const t = e.touches[0];
    lastTouchClient = { x: t.clientX, y: t.clientY };
    canvas.dispatchEvent(new MouseEvent("mousedown", {
      clientX: t.clientX,
      clientY: t.clientY,
      button: 0
    }));
  }
}, { passive: false });

canvas.addEventListener("touchmove", (e) => {
  e.preventDefault();
  if (e.touches.length >= 2 && isTwoFingerGesture) {
    const t1 = e.touches[0];
    const t2 = e.touches[1];

    const currentAngle = Math.atan2(t2.clientY - t1.clientY, t2.clientX - t1.clientX);
    const deltaAngle = currentAngle - lastTouchAngle;
    lastTouchAngle = currentAngle;

    if (atoms.length > 0) {
      const cos = Math.cos(deltaAngle);
      const sin = Math.sin(deltaAngle);

      atoms.forEach((a) => {
        const dx = a.x - rotateCenter.x;
        const dy = a.y - rotateCenter.y;
        a.x = rotateCenter.x + dx * cos - dy * sin;
        a.y = rotateCenter.y + dx * sin + dy * cos;
      });

      arrows.forEach((arr) => {
        const dx1 = arr.x1 - rotateCenter.x;
        const dy1 = arr.y1 - rotateCenter.y;
        arr.x1 = rotateCenter.x + dx1 * cos - dy1 * sin;
        arr.y1 = rotateCenter.y + dx1 * sin + dy1 * cos;

        const dx2 = arr.x2 - rotateCenter.x;
        const dy2 = arr.y2 - rotateCenter.y;
        arr.x2 = rotateCenter.x + dx2 * cos - dy2 * sin;
        arr.y2 = rotateCenter.y + dx2 * sin + dy2 * cos;
      });
    }

    const currentDist = Math.hypot(t2.clientX - t1.clientX, t2.clientY - t1.clientY);
    if (lastTouchDist > 0) {
      const scaleRatio = currentDist / lastTouchDist;
      zoom = Math.max(0.3, Math.min(3.0, zoom * scaleRatio));
      updateZoomBadge();
    }
    lastTouchDist = currentDist;
    draw();
    return;
  }

  if (e.touches.length === 1 && !isTwoFingerGesture) {
    const t = e.touches[0];
    lastTouchClient = { x: t.clientX, y: t.clientY };
    canvas.dispatchEvent(new MouseEvent("mousemove", {
      clientX: t.clientX,
      clientY: t.clientY
    }));
  }
}, { passive: false });

canvas.addEventListener("touchend", (e) => {
  if (e.touches.length === 0) {
    if (!isTwoFingerGesture) {
      window.dispatchEvent(new MouseEvent("mouseup", {
        clientX: lastTouchClient.x,
        clientY: lastTouchClient.y,
        button: 0
      }));
    }
    isTwoFingerGesture = false;
    preTouchSnapshot = null;
    lastTouchDist = 0;
  }
});

// === 動態多邊形環座標計算 (3 ~ 18 員環) ===
function buildPolygonVertices(anchor, sides, dragAngle, attachAtom) {
  const bondLen = 36;
  const radius = bondLen / (2 * Math.sin(Math.PI / sides));
  const vertices = [];

  if (attachAtom) {
    const cx = anchor.x + Math.cos(dragAngle) * radius;
    const cy = anchor.y + Math.sin(dragAngle) * radius;
    const startAngle = dragAngle + Math.PI;
    for (let i = 0; i < sides; i++) {
      const a = startAngle + (i * 2 * Math.PI) / sides;
      vertices.push({
        x: i === 0 ? anchor.x : cx + radius * Math.cos(a),
        y: i === 0 ? anchor.y : cy + radius * Math.sin(a)
      });
    }
  } else {
    for (let i = 0; i < sides; i++) {
      const a = dragAngle + (i * 2 * Math.PI) / sides;
      vertices.push({
        x: anchor.x + radius * Math.cos(a),
        y: anchor.y + radius * Math.sin(a)
      });
    }
  }
  return vertices;
}

function commitPolygonRing(anchor, sides, dragAngle, attachAtom) {
  const vertices = buildPolygonVertices(anchor, sides, dragAngle, attachAtom);
  const ringAtoms = vertices.map((pt, i) => {
    if (i === 0 && attachAtom) return attachAtom;
    const a = { id: Date.now() + Math.random() + i, x: pt.x, y: pt.y, el: "C", charge: 0, lonePairs: 0, implicitH: 2 };
    atoms.push(a);
    return a;
  });

  for (let i = 0; i < sides; i++) {
    bonds.push({
      a1: ringAtoms[i].id,
      a2: ringAtoms[(i + 1) % sides].id,
      order: 1
    });
  }
}

// === 常見取代基幾何定義 ===
function getOutwardAngleForAtom(attachAtom) {
  if (!attachAtom) return 0;
  const bondAngles = [];
  for (const b of bonds) {
    const otherId = b.a1 === attachAtom.id ? b.a2 : b.a2 === attachAtom.id ? b.a1 : null;
    if (otherId !== null) {
      const other = atoms.find((item) => item.id === otherId);
      if (other) {
        bondAngles.push(Math.atan2(other.y - attachAtom.y, other.x - attachAtom.x));
      }
    }
  }
  if (bondAngles.length === 0) return -Math.PI / 6;
  return computeRepulsionAngles(bondAngles, 1)[0];
}

function getSubstituentGeometry(type, anchor, attachAtom) {
  const R = 36;
  const dir = getOutwardAngleForAtom(attachAtom);
  const cos = Math.cos(dir);
  const sin = Math.sin(dir);

  const toWorld = (lx, ly) => ({
    x: anchor.x + lx * cos - ly * sin,
    y: anchor.y + lx * sin + ly * cos
  });

  const deg60 = Math.PI / 3;
  let localAtoms = [];
  let localBonds = [];

  if (type === "CH3") {
    localAtoms = [{ lx: R, ly: 0, el: "C", charge: 0 }];
    localBonds = [{ fromRoot: true, a2: 0, order: 1 }];
  } else if (type === "C2H5") {
    const p1 = { lx: R, ly: 0 };
    const p2 = { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60) };
    localAtoms = [
      { ...p1, el: "C", charge: 0 },
      { ...p2, el: "C", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 1 }
    ];
  } else if (type === "OH") {
    localAtoms = [{ lx: R, ly: 0, el: "O", charge: 0 }];
    localBonds = [{ fromRoot: true, a2: 0, order: 1 }];
  } else if (type === "NH2") {
    localAtoms = [{ lx: R, ly: 0, el: "N", charge: 0 }];
    localBonds = [{ fromRoot: true, a2: 0, order: 1 }];
  } else if (type === "COOH") {
    localAtoms = [
      { lx: R, ly: 0, el: "C", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60), el: "O", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: R * Math.sin(deg60), el: "O", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 2 },
      { a1: 0, a2: 2, order: 1 }
    ];
  } else if (type === "CHO") {
    localAtoms = [
      { lx: R, ly: 0, el: "C", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60), el: "O", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 2 }
    ];
  } else if (type === "NO2") {
    localAtoms = [
      { lx: R, ly: 0, el: "N", charge: 1 },
      { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60), el: "O", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: R * Math.sin(deg60), el: "O", charge: -1 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 2 },
      { a1: 0, a2: 2, order: 1 }
    ];
  } else if (type === "CN") {
    localAtoms = [
      { lx: R, ly: 0, el: "C", charge: 0 },
      { lx: R * 2, ly: 0, el: "N", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 3 }
    ];
  } else if (type === "OCH3") {
    localAtoms = [
      { lx: R, ly: 0, el: "O", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60), el: "C", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 1 }
    ];
  } else if (type === "COCH3") {
    localAtoms = [
      { lx: R, ly: 0, el: "C", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: -R * Math.sin(deg60), el: "O", charge: 0 },
      { lx: R + R * Math.cos(deg60), ly: R * Math.sin(deg60), el: "C", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 2 },
      { a1: 0, a2: 2, order: 1 }
    ];
  } else if (type === "CF3") {
    localAtoms = [
      { lx: R, ly: 0, el: "C", charge: 0 },
      { lx: R + R * 0.5, ly: -R * 0.866, el: "F", charge: 0 },
      { lx: R * 2, ly: 0, el: "F", charge: 0 },
      { lx: R + R * 0.5, ly: R * 0.866, el: "F", charge: 0 }
    ];
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 1 },
      { a1: 0, a2: 2, order: 1 },
      { a1: 0, a2: 3, order: 1 }
    ];
  } else if (type === "Ph") {
    const cx = R * 2;
    for (let i = 0; i < 6; i++) {
      const ang = Math.PI + (i * Math.PI) / 3;
      localAtoms.push({
        lx: cx + R * Math.cos(ang),
        ly: R * Math.sin(ang),
        el: "C",
        charge: 0
      });
    }
    localBonds = [
      { fromRoot: true, a2: 0, order: 1 },
      { a1: 0, a2: 1, order: 2 },
      { a1: 1, a2: 2, order: 1 },
      { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 },
      { a1: 4, a2: 5, order: 2 },
      { a1: 5, a2: 0, order: 1 }
    ];
  } else {
    return null;
  }

  const placedAtoms = localAtoms.map((item) => {
    const pt = toWorld(item.lx, item.ly);
    return { x: pt.x, y: pt.y, el: item.el, charge: item.charge || 0 };
  });

  return { atoms: placedAtoms, bonds: localBonds };
}

function placeSubstituent(type, anchor, attachAtom) {
  const geo = getSubstituentGeometry(type, anchor, attachAtom);
  if (!geo) return;

  let rootAtom = attachAtom;
  if (!rootAtom) {
    rootAtom = {
      id: Date.now() + Math.random(),
      x: anchor.x,
      y: anchor.y,
      el: "C",
      charge: 0,
      lonePairs: 0,
      implicitH: 0
    };
    atoms.push(rootAtom);
  }

  const created = geo.atoms.map((a, idx) => {
    const obj = {
      id: Date.now() + Math.random() + idx + 1,
      x: a.x,
      y: a.y,
      el: a.el,
      charge: a.charge || 0,
      lonePairs: 0,
      implicitH: 0
    };
    atoms.push(obj);
    return obj;
  });

  geo.bonds.forEach((b) => {
    const a1Id = b.fromRoot ? rootAtom.id : created[b.a1].id;
    const a2Id = created[b.a2].id;
    bonds.push({ a1: a1Id, a2: a2Id, order: b.order });
  });
}

// === 芳香環與生醫環模板幾何定義 ===
function getRingTemplateGeometry(type, anchor, attachAtom) {
  const R = 36;
  const hx = (Math.sqrt(3) / 2) * R;
  const hy = 0.5 * R;

  let rawAtoms = [];
  let rawBonds = [];

  if (type === "benzene") {
    const pts = [[0,-2],[1,-1],[1,1],[0,2],[-1,1],[-1,-1]];
    rawAtoms = pts.map(([u, v]) => ({ x: u * hx, y: v * hy, el: "C" }));
    rawBonds = [
      { a1: 0, a2: 1, order: 2 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 2 }, { a1: 5, a2: 0, order: 1 }
    ];
  } else if (type === "naphthalene") {
    const pts = [
      [-1,-2],[0,-1],[0,1],[-1,2],[-2,1],[-2,-1],
      [1,-2],[2,-1],[2,1],[1,2]
    ];
    rawAtoms = pts.map(([u, v]) => ({ x: u * hx, y: v * hy, el: "C" }));
    rawBonds = [
      { a1: 0, a2: 1, order: 2 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 2 }, { a1: 5, a2: 0, order: 1 },
      { a1: 1, a2: 6, order: 1 }, { a1: 6, a2: 7, order: 2 }, { a1: 7, a2: 8, order: 1 },
      { a1: 8, a2: 9, order: 2 }, { a1: 9, a2: 2, order: 1 }
    ];
  } else if (type === "anthracene") {
    const pts = [
      [-2,-2],[-1,-1],[-1,1],[-2,2],[-3,1],[-3,-1],
      [0,-2],[1,-1],[1,1],[0,2],
      [2,-2],[3,-1],[3,1],[2,2]
    ];
    rawAtoms = pts.map(([u, v]) => ({ x: u * hx, y: v * hy, el: "C" }));
    rawBonds = [
      { a1: 0, a2: 1, order: 2 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 2 }, { a1: 5, a2: 0, order: 1 },
      { a1: 1, a2: 6, order: 1 }, { a1: 6, a2: 7, order: 2 }, { a1: 7, a2: 8, order: 1 },
      { a1: 8, a2: 9, order: 2 }, { a1: 9, a2: 2, order: 1 },
      { a1: 7, a2: 10, order: 1 }, { a1: 10, a2: 11, order: 2 }, { a1: 11, a2: 12, order: 1 },
      { a1: 12, a2: 13, order: 2 }, { a1: 13, a2: 8, order: 1 }
    ];
  } else if (type === "phenanthrene") {
    const pts = [
      [-1,-2],[0,-1],[0,1],[-1,2],[-2,1],[-2,-1],
      [1,-2],[2,-1],[2,1],[1,2],
      [-1,-4],[-2,-5],[-3,-4],[-3,-2]
    ];
    rawAtoms = pts.map(([u, v]) => ({ x: u * hx, y: v * hy, el: "C" }));
    rawBonds = [
      { a1: 0, a2: 1, order: 1 }, { a1: 1, a2: 2, order: 2 }, { a1: 2, a2: 3, order: 1 },
      { a1: 3, a2: 4, order: 2 }, { a1: 4, a2: 5, order: 1 }, { a1: 5, a2: 0, order: 2 },
      { a1: 1, a2: 6, order: 1 }, { a1: 6, a2: 7, order: 2 }, { a1: 7, a2: 8, order: 1 },
      { a1: 8, a2: 9, order: 2 }, { a1: 9, a2: 2, order: 1 },
      { a1: 0, a2: 10, order: 1 }, { a1: 10, a2: 11, order: 2 }, { a1: 11, a2: 12, order: 1 },
      { a1: 12, a2: 13, order: 2 }, { a1: 13, a2: 5, order: 1 }
    ];
  } else if (type === "purine") {
    const x1 = hx, y1 = -hy;
    const x2 = hx, y2 = hy;
    const x6 = x1 + R * Math.cos(-Math.PI / 10);
    const y6 = y1 + R * Math.sin(-Math.PI / 10);
    const x8 = x2 + R * Math.cos(Math.PI / 10);
    const y8 = y2 + R * Math.sin(Math.PI / 10);
    const x7 = x6 + R * Math.cos((3 * Math.PI) / 10);
    const y7 = 0;

    rawAtoms = [
      { x: 0, y: -R, el: "C" },
      { x: x1, y: y1, el: "C" },
      { x: x2, y: y2, el: "C" },
      { x: 0, y: R, el: "N" },
      { x: -hx, y: hy, el: "C" },
      { x: -hx, y: -hy, el: "N" },
      { x: x6, y: y6, el: "N" },
      { x: x7, y: y7, el: "C" },
      { x: x8, y: y8, el: "N" }
    ];
    rawBonds = [
      { a1: 0, a2: 1, order: 1 }, { a1: 1, a2: 2, order: 2 }, { a1: 2, a2: 3, order: 1 },
      { a1: 3, a2: 4, order: 2 }, { a1: 4, a2: 5, order: 1 }, { a1: 5, a2: 0, order: 2 },
      { a1: 1, a2: 6, order: 1 }, { a1: 6, a2: 7, order: 2 }, { a1: 7, a2: 8, order: 1 },
      { a1: 8, a2: 2, order: 1 }
    ];
  } else if (type === "pyrimidine") {
    const pts = [[0,-2],[1,-1],[1,1],[0,2],[-1,1],[-1,-1]];
    rawAtoms = pts.map(([u, v], idx) => ({
      x: u * hx,
      y: v * hy,
      el: idx === 0 || idx === 2 ? "N" : "C"
    }));
    rawBonds = [
      { a1: 0, a2: 1, order: 2 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 2 }, { a1: 5, a2: 0, order: 1 }
    ];
  } else if (type === "pyridine") {
    const pts = [[0,-2],[1,-1],[1,1],[0,2],[-1,1],[-1,-1]];
    rawAtoms = pts.map(([u, v], idx) => ({
      x: u * hx,
      y: v * hy,
      el: idx === 0 ? "N" : "C"
    }));
    rawBonds = [
      { a1: 0, a2: 1, order: 2 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 2 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 2 }, { a1: 5, a2: 0, order: 1 }
    ];
  } else if (type === "piperidine") {
    const pts = [[0,-2],[1,-1],[1,1],[0,2],[-1,1],[-1,-1]];
    rawAtoms = pts.map(([u, v], idx) => ({
      x: u * hx,
      y: v * hy,
      el: idx === 0 ? "N" : "C"
    }));
    rawBonds = [
      { a1: 0, a2: 1, order: 1 }, { a1: 1, a2: 2, order: 1 }, { a1: 2, a2: 3, order: 1 },
      { a1: 3, a2: 4, order: 1 }, { a1: 4, a2: 5, order: 1 }, { a1: 5, a2: 0, order: 1 }
    ];
  } else {
    return null;
  }

  let attachIdx = -1;
  let offsetX = anchor.x;
  let offsetY = anchor.y;

  if (attachAtom) {
    attachIdx = rawAtoms.findIndex((a) => a.el === attachAtom.el);
    if (attachIdx === -1) attachIdx = 0;
    offsetX = anchor.x - rawAtoms[attachIdx].x;
    offsetY = anchor.y - rawAtoms[attachIdx].y;
  }

  const placedAtoms = rawAtoms.map((a) => ({
    x: a.x + offsetX,
    y: a.y + offsetY,
    el: a.el
  }));

  return { atoms: placedAtoms, bonds: rawBonds, attachIdx };
}

function placeRingTemplate(type, anchor, attachAtom) {
  const tpl = getRingTemplateGeometry(type, anchor, attachAtom);
  if (!tpl) return;

  const createdAtoms = tpl.atoms.map((a, idx) => {
    if (attachAtom && idx === tpl.attachIdx) {
      return attachAtom;
    }
    const obj = {
      id: Date.now() + Math.random() + idx,
      x: a.x,
      y: a.y,
      el: a.el,
      charge: 0,
      lonePairs: 0,
      implicitH: 0
    };
    atoms.push(obj);
    return obj;
  });

  tpl.bonds.forEach((b) => {
    bonds.push({
      a1: createdAtoms[b.a1].id,
      a2: createdAtoms[b.a2].id,
      order: b.order
    });
  });
}

function bindUIEvents() {
  document.querySelectorAll(".dock-btn[data-tool]").forEach((btn) => {
    btn.addEventListener("click", () => {
      const tool = btn.getAttribute("data-tool");
      if (tool === "bond") currentBondOrder = Number(btn.getAttribute("data-order"));
      if (tool === "ring") currentRingType = btn.getAttribute("data-ring");
      if (tool === "charge") currentChargeVal = Number(btn.getAttribute("data-val"));
      setActiveTool(tool);
    });
  });

  const openRingLibBtn = document.getElementById("openRingLibBtn");
  const closeRingLibBtn = document.getElementById("closeRingLibBtn");
  if (openRingLibBtn) {
    openRingLibBtn.addEventListener("click", () => {
      document.getElementById("ringLibModal").classList.toggle("hidden");
      document.getElementById("subLibModal").classList.add("hidden");
      document.getElementById("ptModal").classList.add("hidden");
    });
  }
  if (closeRingLibBtn) {
    closeRingLibBtn.addEventListener("click", () => {
      document.getElementById("ringLibModal").classList.add("hidden");
    });
  }

  const openSubLibBtn = document.getElementById("openSubLibBtn");
  const closeSubLibBtn = document.getElementById("closeSubLibBtn");
  if (openSubLibBtn) {
    openSubLibBtn.addEventListener("click", () => {
      document.getElementById("subLibModal").classList.toggle("hidden");
      document.getElementById("ringLibModal").classList.add("hidden");
      document.getElementById("ptModal").classList.add("hidden");
    });
  }
  if (closeSubLibBtn) {
    closeSubLibBtn.addEventListener("click", () => {
      document.getElementById("subLibModal").classList.add("hidden");
    });
  }

  document.querySelectorAll(".atom-btn").forEach((btn) => {
    btn.addEventListener("click", () => {
      selectAtomElement(btn.getAttribute("data-atom"));
    });
  });

  const openPtBtn = document.getElementById("openPtBtn");
  const closePtBtn = document.getElementById("closePtBtn");
  if (openPtBtn) {
    openPtBtn.addEventListener("click", () => {
      document.getElementById("ptModal").classList.toggle("hidden");
      document.getElementById("ringLibModal").classList.add("hidden");
      document.getElementById("subLibModal").classList.add("hidden");
    });
  }
  if (closePtBtn) {
    closePtBtn.addEventListener("click", () => {
      document.getElementById("ptModal").classList.add("hidden");
    });
  }

  document.getElementById("btnErase").addEventListener("click", () => {
    setActiveTool("erase");
  });

  document.getElementById("btnClear").addEventListener("click", () => {
    saveState();
    atoms = [];
    bonds = [];
    arrows = [];
    hideArrowControlBar();
    draw();
  });

  document.getElementById("btnUndo").addEventListener("click", () => {
    if (history.length === 0) return;
    redoStack.push(JSON.stringify({ atoms, bonds, arrows }));
    const prev = JSON.parse(history.pop());
    atoms = prev.atoms;
    bonds = prev.bonds;
    arrows = prev.arrows || [];
    hideArrowControlBar();
    syncAllImplicitHydrogens();
    draw();
  });

  document.getElementById("btnRedo").addEventListener("click", () => {
    if (redoStack.length === 0) return;
    history.push(JSON.stringify({ atoms, bonds, arrows }));
    const next = JSON.parse(redoStack.pop());
    atoms = next.atoms;
    bonds = next.bonds;
    arrows = next.arrows || [];
    hideArrowControlBar();
    syncAllImplicitHydrogens();
    draw();
  });

  const btnToggleH = document.getElementById("btnToggleH");
  if (btnToggleH) {
    btnToggleH.addEventListener("click", () => {
      showHydrogens2D = !showHydrogens2D;
      btnToggleH.classList.toggle("active", showHydrogens2D);
      draw();
    });
  }

  document.getElementById("btnArrowCurveUp").addEventListener("click", () => {
    if (!selectedArrow) return;
    saveState();
    const dx = selectedArrow.x2 - selectedArrow.x1;
    const dy = selectedArrow.y2 - selectedArrow.y1;
    const dist = Math.hypot(dx, dy) || 1;
    const ny = dx / dist;
    const upSign = ny >= 0 ? -1 : 1;
    const currentCurve = typeof selectedArrow.curve === "number" ? selectedArrow.curve : 0.35;
    selectedArrow.curve = Math.max(-0.95, Math.min(0.95, currentCurve + upSign * 0.18));
    draw();
  });

  document.getElementById("btnArrowCurveDown").addEventListener("click", () => {
    if (!selectedArrow) return;
    saveState();
    const dx = selectedArrow.x2 - selectedArrow.x1;
    const dy = selectedArrow.y2 - selectedArrow.y1;
    const dist = Math.hypot(dx, dy) || 1;
    const ny = dx / dist;
    const downSign = ny >= 0 ? 1 : -1;
    const currentCurve = typeof selectedArrow.curve === "number" ? selectedArrow.curve : 0.35;
    selectedArrow.curve = Math.max(-0.95, Math.min(0.95, currentCurve + downSign * 0.18));
    draw();
  });

  document.getElementById("btnArrowFlip").addEventListener("click", () => {
    if (!selectedArrow) return;
    saveState();
    const tmpX = selectedArrow.x1;
    const tmpY = selectedArrow.y1;
    selectedArrow.x1 = selectedArrow.x2;
    selectedArrow.y1 = selectedArrow.y2;
    selectedArrow.x2 = tmpX;
    selectedArrow.y2 = tmpY;
    selectedArrow.curve = -(typeof selectedArrow.curve === "number" ? selectedArrow.curve : 0.35);
    draw();
  });

  document.getElementById("btnArrowDelete").addEventListener("click", () => {
    if (!selectedArrow) return;
    saveState();
    arrows = arrows.filter((a) => a !== selectedArrow);
    hideArrowControlBar();
    draw();
  });

  document.getElementById("btnArrowClose").addEventListener("click", () => {
    hideArrowControlBar();
    draw();
  });

  let chairFlipState = false;

  document.getElementById("btnClean").addEventListener("click", () => {
    if (atoms.length === 0) return;
    const molfile = exportCanvasToMolfile();
    if (!molfile) return;

    try {
      const savedLonePairs = atoms.map((a) => a.lonePairs || 0);
      const savedCharges = atoms.map((a) => a.charge || 0);
      const mol = OCL.Molecule.fromMolfile(molfile);
      mol.inventCoordinates();
      mol.ensureHelperArrays(7);

      const nAtoms = mol.getAllAtoms();
      const nBonds = mol.getAllBonds();
      const newAtoms = [];
      let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;

      for (let i = 0; i < nAtoms; i++) {
        const x = mol.getAtomX(i) * 34;
        const y = mol.getAtomY(i) * 34;
        minX = Math.min(minX, x); maxX = Math.max(maxX, x);
        minY = Math.min(minY, y); maxY = Math.max(maxY, y);
        newAtoms.push({
          id: i + 1,
          x, y,
          el: mol.getAtomLabel(i) || "C",
          charge: savedCharges[i] !== undefined ? savedCharges[i] : (mol.getAtomCharge(i) || 0),
          lonePairs: savedLonePairs[i] || 0,
          implicitH: 0
        });
      }

      const oldCenterX = atoms.reduce((s, a) => s + a.x, 0) / atoms.length;
      const oldCenterY = atoms.reduce((s, a) => s + a.y, 0) / atoms.length;
      const offsetX = oldCenterX - (minX + maxX) / 2;
      const offsetY = oldCenterY - (minY + maxY) / 2;
      newAtoms.forEach((a) => { a.x += offsetX; a.y += offsetY; });

      const newBonds = [];
      for (let i = 0; i < nBonds; i++) {
        newBonds.push({
          a1: mol.getBondAtom(0, i) + 1,
          a2: mol.getBondAtom(1, i) + 1,
          order: mol.getBondOrder(i) || 1
        });
      }

      saveState();
      atoms = newAtoms;
      bonds = newBonds;
      syncAllImplicitHydrogens();
      draw();
    } catch (err) {
      showAlert("無法自動重整此結構，請確認化學鍵連線是否有效", "warning");
    }
  });

  document.getElementById("btnChair").addEventListener("click", () => {
    const ring6 = findSixMemberedRing();
    if (!ring6) {
      showAlert("畫布中找不到封閉的六員環結構！", "warning");
      return;
    }

    saveState();
    const beforeCenterX = atoms.reduce((s, a) => s + a.x, 0) / atoms.length;
    const beforeCenterY = atoms.reduce((s, a) => s + a.y, 0) / atoms.length;

    const ringCx = ring6.reduce((s, a) => s + a.x, 0) / 6;
    const ringCy = ring6.reduce((s, a) => s + a.y, 0) / 6;

    const chairOffsets = !chairFlipState
      ? [
          { dx: -46, dy:  12 },
          { dx: -14, dy: -14 },
          { dx:  26, dy:  -4 },
          { dx:  46, dy: -20 },
          { dx:  14, dy:  16 },
          { dx: -26, dy:  10 }
        ]
      : [
          { dx: -46, dy: -20 },
          { dx: -14, dy:  16 },
          { dx:  26, dy:  10 },
          { dx:  46, dy:  12 },
          { dx:  14, dy: -14 },
          { dx: -26, dy:  -4 }
        ];

    chairFlipState = !chairFlipState;
    const movedSet = new Set(ring6.map((r) => r.id));

    ring6.forEach((atom, idx) => {
      const targetX = ringCx + chairOffsets[idx].dx;
      const targetY = ringCy + chairOffsets[idx].dy;
      const moveX = targetX - atom.x;
      const moveY = targetY - atom.y;

      moveSubstituents(atom.id, movedSet, moveX, moveY);
      atom.x = targetX;
      atom.y = targetY;
    });

    const afterCenterX = atoms.reduce((s, a) => s + a.x, 0) / atoms.length;
    const afterCenterY = atoms.reduce((s, a) => s + a.y, 0) / atoms.length;
    const fixX = beforeCenterX - afterCenterX;
    const fixY = beforeCenterY - afterCenterY;

    atoms.forEach((a) => {
      a.x += fixX;
      a.y += fixY;
    });

    draw();
  });

  document.getElementById("btnCenter").addEventListener("click", () => {
    if (atoms.length === 0) return;
    const rect = canvas.parentElement.getBoundingClientRect();
    const avgX = atoms.reduce((s, a) => s + a.x, 0) / atoms.length;
    const avgY = atoms.reduce((s, a) => s + a.y, 0) / atoms.length;
    const dx = rect.width / 2 - avgX;
    const dy = rect.height / 2 + (isMobileView() ? 38 : 0) - avgY;
    atoms.forEach((a) => { a.x += dx; a.y += dy; });
    arrows.forEach((arr) => { arr.x1 += dx; arr.y1 += dy; arr.x2 += dx; arr.y2 += dy; });
    draw();
  });

  document.getElementById("btnZoomIn").addEventListener("click", () => {
    zoom = Math.min(3.0, zoom + 0.12);
    updateZoomBadge();
    draw();
  });

  document.getElementById("btnZoomOut").addEventListener("click", () => {
    zoom = Math.max(0.3, Math.min(3.0, zoom - 0.12));
    updateZoomBadge();
    draw();
  });

  document.getElementById("toggle3DBtn").addEventListener("click", () => {
    if (isMobileView()) {
      mobileActivePane = mobileActivePane === "2d" ? "3d" : "2d";
    } else {
      desktopShow3D = !desktopShow3D;
    }
    applyResponsiveLayout();
  });

  // 手機版 3D 畫面左上角「← 返回 2D 編輯」按鈕
  const backTo2DBtn = document.getElementById("backTo2DBtn");
  if (backTo2DBtn) {
    backTo2DBtn.addEventListener("click", () => {
      mobileActivePane = "2d";
      applyResponsiveLayout();
    });
  }

  // 轉 3D 按鈕
  document.getElementById("syncBtn").addEventListener("click", () => {
    if (atoms.length === 0) {
      showAlert("畫布目前沒有分子結構，請先繪製或搜尋分子！", "info");
      return;
    }
    syncAllImplicitHydrogens();
    const components = getAllConnectedComponents();

    if (components.length > 1) {
      renderMultiMolecule3D(components);
      if (isMobileView()) {
        mobileActivePane = "3d";
        applyResponsiveLayout();
      }
      return;
    }

    const molfile = exportCanvasToMolfile();
    if (!molfile) return;
    try {
      const oclMol = OCL.Molecule.fromMolfile(molfile);
      const hasCharge = atoms.some((a) => (a.charge || 0) !== 0);
      if (hasCharge) {
        generateLocal3DFromMol(oclMol, oclMol.toSmiles() || "Charged Species", atoms);
      } else {
        const smiles = oclMol.toSmiles();
        if (smiles) {
          processMolecule(smiles, false);
        }
      }
      if (isMobileView()) {
        mobileActivePane = "3d";
        applyResponsiveLayout();
      }
    } catch (err) {
      showAlert("請確認畫布上的化學結構連線完整", "warning");
    }
  });

  setupSearchAutocomplete();

  document.getElementById("styleSelect").addEventListener("change", (e) => {
    apply3DStyle(e.target.value);
  });

  document.getElementById("exportBtn").addEventListener("click", () => {
    if (!currentSdfData) {
      showAlert("目前尚無可匯出的 3D 分子資料，請先點擊「轉 3D」！", "info");
      return;
    }
    const blob = new Blob([currentSdfData], { type: "chemical/x-mdl-sdfile" });
    const a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = "molecule_3d.sdf";
    a.click();
  });

  document.getElementById("torsionSlider").addEventListener("input", (e) => {
    const deg = Number(e.target.value);
    document.getElementById("torsionAngleLabel").textContent = `${deg}°`;

    const mod120 = deg % 120;
    const statusEl = document.getElementById("torsionStatus");
    if (mod120 <= 8 || mod120 >= 112) {
      statusEl.textContent = "✦ 交錯式 (Staggered · 能量最低)";
      statusEl.style.color = "#38bdf8";
    } else if (Math.abs(mod120 - 60) <= 8) {
      statusEl.textContent = "⚡ 重疊式 (Eclipsed · 能量最高)";
      statusEl.style.color = "#fbbf24";
    } else {
      statusEl.textContent = "過渡扭轉角 (Skew)";
      statusEl.style.color = "#94a3b8";
    }

    const bondIdx = Number(document.getElementById("bondSelect").value);
    const targetBond = rotatableBonds[bondIdx];
    if (!targetBond) return;

    const pA = base3DAtoms[targetBond.a1];
    const pB = base3DAtoms[targetBond.a2];

    let ux = pB.x - pA.x;
    let uy = pB.y - pA.y;
    let uz = pB.z - pA.z;
    const len = Math.hypot(ux, uy, uz) || 1;
    ux /= len; uy /= len; uz /= len;

    const rad = (deg * Math.PI) / 180;
    const cos = Math.cos(rad);
    const sin = Math.sin(rad);

    const rotatedAtoms = base3DAtoms.map((a) => ({ ...a }));
    targetBond.movingIndices.forEach((idx) => {
      if (idx === targetBond.a2) return;
      const atom = rotatedAtoms[idx];
      const vx = atom.x - pB.x;
      const vy = atom.y - pB.y;
      const vz = atom.z - pB.z;

      const dot = ux * vx + uy * vy + uz * vz;
      const crossX = uy * vz - uz * vy;
      const crossY = uz * vx - ux * vz;
      const crossZ = ux * vy - uy * vx;

      atom.x = pB.x + vx * cos + crossX * sin + ux * dot * (1 - cos);
      atom.y = pB.y + vy * cos + crossY * sin + uz * dot * (1 - cos);
      atom.z = pB.z + vz * cos + crossZ * sin + uz * dot * (1 - cos);
    });

    const newSdf = buildSdfFromAtoms(rotatedAtoms, base3DBonds);
    viewer3D.clear();
    viewer3D.addModel(newSdf, "sdf");
    apply3DStyle(document.getElementById("styleSelect").value);
  });

  document.getElementById("bondSelect").addEventListener("change", () => {
    document.getElementById("torsionSlider").value = 0;
    document.getElementById("torsionAngleLabel").textContent = "0°";
  });
}

// 確保 3D 結構的隱含氫原子與 2D 畫面同步一致
function applyTargetHydrogensToOclMol(mol, sourceAtoms) {
  mol.ensureHelperArrays(7);
  if (Array.isArray(sourceAtoms)) {
    sourceAtoms.forEach((srcAtom, idx) => {
      if (idx >= mol.getAllAtoms() || srcAtom.el === "H") return;
      const desiredH = getImplicitHydrogens(srcAtom);
      const currentH = mol.getImplicitHydrogens(idx);
      const diff = desiredH - currentH;
      if (diff > 0) {
        for (let k = 0; k < diff; k++) {
          const hIdx = mol.addAtom(1);
          mol.addBond(idx, hIdx, 1);
        }
      }
    });
  }
  mol.addImplicitHydrogens();
}

// === 多分子同時 3D 渲染 ===
function renderMultiMolecule3D(components) {
  const infoEl = document.getElementById("molInfo");
  const badgeEl = document.getElementById("sourceBadge");
  const formulaEl = document.getElementById("molFormula");

  try {
    const globalCx = atoms.reduce((s, a) => s + a.x, 0) / atoms.length;
    const globalCy = atoms.reduce((s, a) => s + a.y, 0) / atoms.length;
    const scale2Dto3D = 1.52 / 36;

    const mergedAtoms = [];
    const mergedBonds = [];
    const formulaParts = [];
    let totalWeight = 0;

    components.forEach((comp, compIdx) => {
      const compCx = comp.atoms.reduce((s, a) => s + a.x, 0) / comp.atoms.length;
      const compCy = comp.atoms.reduce((s, a) => s + a.y, 0) / comp.atoms.length;
      const shiftX = (compCx - globalCx) * scale2Dto3D;
      const shiftY = -(compCy - globalCy) * scale2Dto3D;

      const subMolfile = buildMolfileForSubset(comp.atoms, comp.bonds, `Comp_${compIdx + 1}`);
      const mol = OCL.Molecule.fromMolfile(subMolfile);
      applyTargetHydrogensToOclMol(mol, comp.atoms);

      const fObj = mol.getMolecularFormula();
      if (fObj && fObj.formula) {
        formulaParts.push(fObj.formula);
        totalWeight += fObj.relativeWeight || 0;
      }

      let mol3D = null;
      try {
        const generator = new OCL.ConformerGenerator(1);
        mol3D = generator.getOneConformerAsMolecule(mol);
      } catch (e) {
        mol3D = null;
      }

      const baseIndex = mergedAtoms.length;

      if (mol3D) {
        const nA = mol3D.getAllAtoms();
        const nB = mol3D.getAllBonds();
        let c3x = 0, c3y = 0, c3z = 0;
        for (let i = 0; i < nA; i++) {
          c3x += mol3D.getAtomX(i);
          c3y += mol3D.getAtomY(i);
          c3z += mol3D.getAtomZ(i);
        }
        c3x /= Math.max(1, nA);
        c3y /= Math.max(1, nA);
        c3z /= Math.max(1, nA);

        for (let i = 0; i < nA; i++) {
          mergedAtoms.push({
            x: mol3D.getAtomX(i) - c3x + shiftX,
            y: mol3D.getAtomY(i) - c3y + shiftY,
            z: mol3D.getAtomZ(i) - c3z,
            el: mol3D.getAtomLabel(i) || "C",
            charge: mol3D.getAtomCharge(i) || 0
          });
        }
        for (let i = 0; i < nB; i++) {
          mergedBonds.push({
            a1: baseIndex + mol3D.getBondAtom(0, i),
            a2: baseIndex + mol3D.getBondAtom(1, i),
            order: mol3D.getBondOrder(i) || 1
          });
        }
      } else {
        const localMap = new Map();
        comp.atoms.forEach((a, i) => {
          localMap.set(a.id, baseIndex + i);
          mergedAtoms.push({
            x: (a.x - compCx) * scale2Dto3D + shiftX,
            y: -(a.y - compCy) * scale2Dto3D + shiftY,
            z: 0,
            el: a.el || "C",
            charge: a.charge || 0
          });
        });
        comp.bonds.forEach((b) => {
          mergedBonds.push({
            a1: localMap.get(b.a1),
            a2: localMap.get(b.a2),
            order: b.order || 1
          });
        });
      }
    });

    currentSdfData = buildSdfFromAtoms(mergedAtoms, mergedBonds);
    badgeEl.className = "badge local";
    badgeEl.textContent = `⚡ 多分子 3D (${components.length} 個)`;
    formulaEl.textContent = `${formulaParts.join(" + ")} (${totalWeight.toFixed(2)})`;
    infoEl.textContent = `已同步渲染 ${components.length} 個獨立分子與相對空間位置`;

    render3DModel(currentSdfData);
  } catch (err) {
    console.error("多分子 3D 轉換失敗:", err);
    badgeEl.className = "badge local";
    badgeEl.textContent = "錯誤";
    infoEl.textContent = "多分子 3D 構象生成失敗，請檢查化學鍵連線";
  }
}

function setupSearchAutocomplete() {
  const input = document.getElementById("searchInput");
  const listEl = document.getElementById("searchSuggestions");
  const searchWrap = document.getElementById("searchWrap");
  const topMenu = document.querySelector(".top-menu");
  let debounceTimer = null;
  let activeFetchController = null;
  let activeIndex = -1;
  let currentSuggestions = [];

  function positionSearchSuggestions() {
    if (listEl.classList.contains("hidden") || !searchWrap) return;
    const rect = searchWrap.getBoundingClientRect();
    listEl.style.top = `${rect.bottom + 6}px`;
    const maxLeft = Math.max(8, window.innerWidth - 250);
    listEl.style.left = `${Math.max(8, Math.min(rect.left, maxLeft))}px`;
    listEl.style.minWidth = `${Math.max(230, rect.width)}px`;
  }

  if (topMenu) {
    topMenu.addEventListener("scroll", positionSearchSuggestions, { passive: true });
  }
  window.addEventListener("resize", positionSearchSuggestions);

  function submitSearch(queryVal) {
    const val = queryVal.trim();
    if (!val) return;
    listEl.classList.add("hidden");
    const isSmiles = /^[A-Za-z0-9@+\-\[\]\(\)\\\/%=#$]+$/.test(val) && /[=\(\)\[\]#1-9]/.test(val);
    processMolecule(val, !isSmiles);
  }

  function renderSuggestions(items) {
    currentSuggestions = items;
    activeIndex = -1;
    if (!items || items.length === 0) {
      listEl.classList.add("hidden");
      listEl.innerHTML = "";
      return;
    }

    listEl.innerHTML = "";
    items.forEach((item) => {
      const div = document.createElement("div");
      div.className = "search-item";
      if (item.zh) {
        div.innerHTML = `<span>${item.zh}</span><span class="sub-name">${item.en}</span>`;
      } else {
        div.innerHTML = `<span>${item.en}</span>`;
      }
      div.addEventListener("pointerdown", (e) => {
        e.preventDefault();
        input.value = item.en;
        submitSearch(item.en);
      });
      listEl.appendChild(div);
    });
    listEl.classList.remove("hidden");
    positionSearchSuggestions();
  }

  function handleQueryChange() {
    const q = input.value.trim();
    clearTimeout(debounceTimer);
    if (activeFetchController) {
      activeFetchController.abort();
      activeFetchController = null;
    }

    if (!q) {
      renderSuggestions([]);
      return;
    }

    const qLower = q.toLowerCase();
    const localMatches = LOCAL_COMPOUNDS.filter(
      (c) => c.zh.toLowerCase().includes(qLower) || c.en.toLowerCase().includes(qLower)
    ).slice(0, 6);

    renderSuggestions(localMatches);

    if (/^[A-Za-z0-9\- ]{2,}$/.test(q)) {
      debounceTimer = setTimeout(async () => {
        const controller = new AbortController();
        activeFetchController = controller;
        try {
          const res = await fetch(
            `https://pubchem.ncbi.nlm.nih.gov/rest/autocomplete/compound/${encodeURIComponent(q)}/json?limit=8`,
            { signal: controller.signal }
          );
          if (!res.ok) return;
          const data = await res.json();
          const terms = data?.dictionary_terms?.compound || [];
          const existingEn = new Set(localMatches.map((m) => m.en.toLowerCase()));
          const merged = [...localMatches];
          terms.forEach((t) => {
            if (!existingEn.has(t.toLowerCase()) && merged.length < 8) {
              merged.push({ zh: "", en: t });
            }
          });
          if (input.value.trim() === q) {
            renderSuggestions(merged);
          }
        } catch (err) {
          // 請求取消或離線時維持本地分子清單
        }
      }, 200);
    }
  }

  input.addEventListener("input", handleQueryChange);
  input.addEventListener("focus", () => {
    if (input.value.trim()) {
      handleQueryChange();
    }
  });

  input.addEventListener("keydown", (e) => {
    const itemEls = listEl.querySelectorAll(".search-item");
    if (e.key === "ArrowDown" && itemEls.length > 0) {
      e.preventDefault();
      activeIndex = (activeIndex + 1) % itemEls.length;
      itemEls.forEach((el, i) => el.classList.toggle("active", i === activeIndex));
    } else if (e.key === "ArrowUp" && itemEls.length > 0) {
      e.preventDefault();
      activeIndex = (activeIndex - 1 + itemEls.length) % itemEls.length;
      itemEls.forEach((el, i) => el.classList.toggle("active", i === activeIndex));
    } else if (e.key === "Escape") {
      listEl.classList.add("hidden");
    } else if (e.key === "Enter") {
      e.preventDefault();
      if (activeIndex >= 0 && currentSuggestions[activeIndex]) {
        const chosen = currentSuggestions[activeIndex].en;
        input.value = chosen;
        submitSearch(chosen);
      } else {
        submitSearch(input.value);
      }
    }
  });

  document.addEventListener("pointerdown", (e) => {
    if (!searchWrap.contains(e.target) && !listEl.contains(e.target)) {
      listEl.classList.add("hidden");
    }
  });
}

function init3DViewer() {
  viewer3D = $3Dmol.createViewer("viewer_3d", { backgroundColor: "#0f172a" });
}

async function processMolecule(query, isName = false) {
  const infoEl = document.getElementById("molInfo");
  const badgeEl = document.getElementById("sourceBadge");
  const formulaEl = document.getElementById("molFormula");

  let searchQuery = query;

  if (isName && /[\u4e00-\u9fa5]/.test(query)) {
    infoEl.textContent = `正在將「${query}」翻譯為英文化學名...`;
    const localHit = LOCAL_COMPOUNDS.find((c) => c.zh.includes(query));
    if (localHit) {
      searchQuery = localHit.en;
    } else {
      try {
        const transRes = await fetch(
          `https://api.mymemory.translated.net/get?q=${encodeURIComponent(query)}&langpair=zh-TW|en`
        );
        const transData = await transRes.json();
        if (transData?.responseData?.translatedText) {
          searchQuery = transData.responseData.translatedText.toLowerCase().trim();
        }
      } catch (e) {
        console.warn("自動翻譯連線失敗:", e);
      }
    }
  }

  infoEl.textContent = `正在向資料庫檢索「${searchQuery}」...`;

  try {
    const type = isName ? "name" : "smiles";
    const encoded = encodeURIComponent(searchQuery);

    const propRes = await fetch(
      `https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/${type}/${encoded}/property/MolecularFormula,MolecularWeight,IUPACName,IsomericSMILES,CanonicalSMILES/JSON`
    );

    if (propRes.ok) {
      const propData = await propRes.json();
      const props = propData.PropertyTable.Properties[0];
      const exactSmiles = props.IsomericSMILES || props.CanonicalSMILES || props.SMILES;

      const sdfTarget = exactSmiles ? `smiles/${encodeURIComponent(exactSmiles)}` : `${type}/${encoded}`;
      const sdfRes = await fetch(
        `https://pubchem.ncbi.nlm.nih.gov/rest/pug/compound/${sdfTarget}/SDF?record_type=3d`
      );

      badgeEl.className = "badge cloud";
      badgeEl.textContent = "☁ PubChem";
      formulaEl.textContent = `${props.MolecularFormula} (${props.MolecularWeight})`;
      infoEl.textContent = `${searchQuery} ｜ ${props.IUPACName || ""}`;

      if (isName && exactSmiles) {
        loadSmilesTo2D(exactSmiles);
      }

      if (sdfRes.ok) {
        currentSdfData = await sdfRes.text();
        render3DModel(currentSdfData);
      } else if (exactSmiles) {
        generateLocal3D(exactSmiles);
      }
      return;
    }

    if (!isName) {
      generateLocal3D(searchQuery);
    } else {
      throw new Error(`資料庫找不到「${searchQuery}」（請嘗試輸入英文名或 SMILES）`);
    }
  } catch (err) {
    if (!isName) {
      generateLocal3D(searchQuery);
    } else {
      badgeEl.className = "badge local";
      badgeEl.textContent = "提示";
      formulaEl.textContent = "—";
      infoEl.textContent = err.message;
    }
  }
}

function generateLocal3DFromMol(mol, labelText, sourceAtoms = null) {
  const infoEl = document.getElementById("molInfo");
  const badgeEl = document.getElementById("sourceBadge");
  const formulaEl = document.getElementById("molFormula");

  try {
    applyTargetHydrogensToOclMol(mol, sourceAtoms);
    const generator = new OCL.ConformerGenerator(1);
    const mol3D = generator.getOneConformerAsMolecule(mol);
    if (!mol3D) throw new Error("無法生成 3D 座標");

    currentSdfData = mol3D.toMolfileV3();
    const formulaObj = mol.getMolecularFormula();

    badgeEl.className = "badge local";
    badgeEl.textContent = "⚡ 本地演算";
    formulaEl.textContent = `${formulaObj.formula} (${formulaObj.relativeWeight.toFixed(2)})`;
    infoEl.textContent = `SMILES: ${labelText}`;

    render3DModel(currentSdfData);
  } catch (localErr) {
    badgeEl.className = "badge local";
    badgeEl.textContent = "錯誤";
    formulaEl.textContent = "—";
    infoEl.textContent = localErr.message;
  }
}

function generateLocal3D(smiles) {
  try {
    const mol = OCL.Molecule.fromSmiles(smiles);
    generateLocal3DFromMol(mol, smiles);
  } catch (localErr) {
    const infoEl = document.getElementById("molInfo");
    const badgeEl = document.getElementById("sourceBadge");
    const formulaEl = document.getElementById("molFormula");
    badgeEl.className = "badge local";
    badgeEl.textContent = "錯誤";
    formulaEl.textContent = "—";
    infoEl.textContent = localErr.message;
  }
}

function parseSdfForRotation(sdfText) {
  const lines = sdfText.split(/\r?\n/);
  if (lines.length < 4) return null;

  const countsLine = lines[3];

  if (countsLine.includes("V3000")) {
    const parsedAtoms = [];
    const parsedBonds = [];
    let inAtomBlock = false;
    let inBondBlock = false;

    for (const line of lines) {
      const trimmed = line.trim();
      if (trimmed === "M  V30 BEGIN ATOM") { inAtomBlock = true; continue; }
      if (trimmed === "M  V30 END ATOM") { inAtomBlock = false; continue; }
      if (trimmed === "M  V30 BEGIN BOND") { inBondBlock = true; continue; }
      if (trimmed === "M  V30 END BOND") { inBondBlock = false; continue; }

      if (inAtomBlock && trimmed.startsWith("M  V30 ")) {
        const parts = trimmed.slice(7).trim().split(/\s+/);
        parsedAtoms.push({
          idx: parseInt(parts[0], 10) - 1,
          el: parts[1],
          x: parseFloat(parts[2]),
          y: parseFloat(parts[3]),
          z: parseFloat(parts[4])
        });
      } else if (inBondBlock && trimmed.startsWith("M  V30 ")) {
        const parts = trimmed.slice(7).trim().split(/\s+/);
        parsedBonds.push({
          order: parseInt(parts[1], 10),
          a1: parseInt(parts[2], 10) - 1,
          a2: parseInt(parts[3], 10) - 1
        });
      }
    }
    return parsedAtoms.length > 0 ? { parsedAtoms, parsedBonds } : null;
  }

  const nAtoms = parseInt(countsLine.slice(0, 3).trim(), 10);
  const nBonds = parseInt(countsLine.slice(3, 6).trim(), 10);
  if (isNaN(nAtoms) || isNaN(nBonds)) return null;

  const parsedAtoms = [];
  for (let i = 0; i < nAtoms; i++) {
    const l = lines[4 + i];
    if (!l) continue;
    parsedAtoms.push({
      idx: i,
      x: parseFloat(l.slice(0, 10)),
      y: parseFloat(l.slice(10, 20)),
      z: parseFloat(l.slice(20, 30)),
      el: l.slice(31, 34).trim()
    });
  }

  const parsedBonds = [];
  for (let i = 0; i < nBonds; i++) {
    const l = lines[4 + nAtoms + i];
    if (!l) continue;
    parsedBonds.push({
      a1: parseInt(l.slice(0, 3).trim(), 10) - 1,
      a2: parseInt(l.slice(3, 6).trim(), 10) - 1,
      order: parseInt(l.slice(6, 9).trim(), 10)
    });
  }

  return { parsedAtoms, parsedBonds };
}

function setupRotatableBonds(sdfText) {
  const box = document.getElementById("torsionBox");
  const select = document.getElementById("bondSelect");
  const slider = document.getElementById("torsionSlider");
  const angleLabel = document.getElementById("torsionAngleLabel");
  const statusEl = document.getElementById("torsionStatus");

  const parsed = parseSdfForRotation(sdfText);
  if (!parsed) {
    box.style.display = "none";
    return;
  }

  base3DAtoms = parsed.parsedAtoms;
  base3DBonds = parsed.parsedBonds;
  rotatableBonds = [];

  base3DBonds.forEach((b) => {
    if (b.order !== 1) return;
    const deg1 = base3DBonds.filter((x) => x.a1 === b.a1 || x.a2 === b.a1).length;
    const deg2 = base3DBonds.filter((x) => x.a1 === b.a2 || x.a2 === b.a2).length;
    if (deg1 < 2 || deg2 < 2) return;

    const groupB = getSubtreeAtoms(b.a2, b.a1);
    if (!groupB.has(b.a1)) {
      const atomA = base3DAtoms[b.a1];
      const atomB = base3DAtoms[b.a2];
      rotatableBonds.push({
        a1: b.a1,
        a2: b.a2,
        label: `${atomA.el}${b.a1 + 1} - ${atomB.el}${b.a2 + 1}`,
        movingIndices: Array.from(groupB)
      });
    }
  });

  if (rotatableBonds.length === 0) {
    box.style.display = "none";
    return;
  }

  select.innerHTML = "";
  rotatableBonds.forEach((rb, i) => {
    const opt = document.createElement("option");
    opt.value = i;
    opt.textContent = `軸: ${rb.label}`;
    select.appendChild(opt);
  });

  slider.value = 0;
  angleLabel.textContent = "0°";
  statusEl.textContent = "初始能量最低構象 (Staggered)";
  box.style.display = "block";
}

function getSubtreeAtoms(startIdx, blockedIdx) {
  const visited = new Set([startIdx]);
  const queue = [startIdx];
  while (queue.length > 0) {
    const curr = queue.shift();
    base3DBonds.forEach((b) => {
      const next = b.a1 === curr ? b.a2 : b.a2 === curr ? b.a1 : null;
      if (next !== null && next !== blockedIdx && !visited.has(next)) {
        visited.add(next);
        queue.push(next);
      }
    });
  }
  return visited;
}

function buildSdfFromAtoms(atomList, bondList) {
  const lines = [
    "MolView",
    "  Multi3D",
    "",
    `${String(atomList.length).padStart(3)}${String(bondList.length).padStart(3)}  0  0  0  0  0  0  0  0999 V2000`
  ];
  const chargedEntries = [];
  atomList.forEach((a, i) => {
    const chgCode = a.charge === 1 ? "  3" : a.charge === -1 ? "  5" : "  0";
    lines.push(
      `${a.x.toFixed(4).padStart(10)}${a.y.toFixed(4).padStart(10)}${a.z.toFixed(4).padStart(10)} ${a.el.padEnd(3)} 0${chgCode}  0  0  0  0  0  0  0  0  0  0`
    );
    if (a.charge && a.charge !== 0) {
      chargedEntries.push({ idx: i + 1, charge: a.charge });
    }
  });
  bondList.forEach((b) => {
    lines.push(`${String(b.a1 + 1).padStart(3)}${String(b.a2 + 1).padStart(3)}${String(b.order).padStart(3)}  0  0  0  0`);
  });
  for (let i = 0; i < chargedEntries.length; i += 8) {
    const chunk = chargedEntries.slice(i, i + 8);
    const entriesStr = chunk
      .map((item) => `${String(item.idx).padStart(4)}${String(item.charge).padStart(4)}`)
      .join("");
    lines.push(`M  CHG${String(chunk.length).padStart(3)}${entriesStr}`);
  }
  lines.push("M  END");
  return lines.join("\n");
}

function render3DModel(molData) {
  if (!viewer3D) return;
  viewer3D.clear();
  viewer3D.addModel(molData, "sdf");
  apply3DStyle(document.getElementById("styleSelect").value);
  viewer3D.resize();
  viewer3D.zoomTo();
  viewer3D.render();
  setupRotatableBonds(molData);
}

function apply3DStyle(styleType) {
  if (!viewer3D) return;
  if (styleType === "stick") {
    viewer3D.setStyle({}, { stick: { radius: 0.16 }, sphere: { scale: 0.26 } });
  } else if (styleType === "sphere") {
    viewer3D.setStyle({}, { sphere: {} });
  } else if (styleType === "line") {
    viewer3D.setStyle({}, { line: { linewidth: 2 } });
  }
  viewer3D.render();
}

function findSixMemberedRing() {
  const adj = new Map();
  atoms.forEach((a) => adj.set(a.id, []));
  bonds.forEach((b) => {
    if (adj.has(b.a1) && adj.has(b.a2)) {
      adj.get(b.a1).push(b.a2);
      adj.get(b.a2).push(b.a1);
    }
  });

  function dfs(startId, currId, path) {
    if (path.length === 6) {
      return adj.get(currId).includes(startId) ? path : null;
    }
    for (const nextId of adj.get(currId)) {
      if (!path.includes(nextId)) {
        const res = dfs(startId, nextId, [...path, nextId]);
        if (res) return res;
      }
    }
    return null;
  }

  for (const a of atoms) {
    const cycleIds = dfs(a.id, a.id, [a.id]);
    if (cycleIds) {
      return cycleIds.map((id) => atoms.find((atom) => atom.id === id));
    }
  }
  return null;
}

function moveSubstituents(rootId, movedSet, dx, dy) {
  const queue = [rootId];
  while (queue.length > 0) {
    const curr = queue.shift();
    bonds.forEach((b) => {
      const neighbor = b.a1 === curr ? b.a2 : b.a2 === curr ? b.a1 : null;
      if (neighbor && !movedSet.has(neighbor)) {
        movedSet.add(neighbor);
        const atomObj = atoms.find((a) => a.id === neighbor);
        if (atomObj) {
          atomObj.x += dx;
          atomObj.y += dy;
        }
        queue.push(neighbor);
      }
    });
  }
}

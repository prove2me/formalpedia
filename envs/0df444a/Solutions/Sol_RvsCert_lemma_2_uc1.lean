-- Prove2me | solution 1 for RvsCert.lemma_2_uc1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-16T07:22:22.696208+00:00
-- url     : https://prove2.me/submissions/69d39626-bac7-48e9-aec1-b2691e88fa33

import Theorems.Thm_RvsCert_lemma_2_unique
import Definitions.Def_RvsCert_randQC
import Definitions.Def_RvsCert_champion
import Definitions.Def_RvsCert_C1
import Definitions.Def_RvsCert_UC1

open RvsCert QAlgorithms

namespace RvsCertL3

/-! ### Generic decision-tree combinators -/

section Generic

variable {ι : Type}

def bindT {α β : Type} : DecisionTree ι Bool α → (α → DecisionTree ι Bool β) → DecisionTree ι Bool β
  | .leaf a, k => k a
  | .node i next, k => .node i (fun b => bindT (next b) k)

theorem eval_bindT {α β : Type} (t : DecisionTree ι Bool α) (k : α → DecisionTree ι Bool β)
    (x : ι → Bool) : (bindT t k).eval x = (k (t.eval x)).eval x := by
  induction t with
  | leaf a => rfl
  | node i next ih => exact ih (x i)

theorem queries_bindT {α β : Type} (t : DecisionTree ι Bool α) (k : α → DecisionTree ι Bool β)
    (x : ι → Bool) : (bindT t k).queries x = t.queries x + (k (t.eval x)).queries x := by
  induction t with
  | leaf a => simp [bindT, DecisionTree.queries, DecisionTree.eval]
  | node i next ih =>
    simp only [bindT, DecisionTree.queries, DecisionTree.eval]
    rw [ih]
    omega

/-- Run `g c` for each `c` of a list, collecting the results. -/
def seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) : List γ → DecisionTree ι Bool (List δ)
  | [] => .leaf []
  | c :: l => bindT (g c) fun d => bindT (seqList g l) fun ds => .leaf (d :: ds)

theorem eval_seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ) (x : ι → Bool) :
    (seqList g l).eval x = l.map fun c => (g c).eval x := by
  induction l with
  | nil => rfl
  | cons c l ih => simp only [seqList, eval_bindT, DecisionTree.eval, ih, List.map_cons]

theorem queries_seqList {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ) (x : ι → Bool) :
    (seqList g l).queries x = (l.map fun c => (g c).queries x).sum := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [seqList, queries_bindT, eval_bindT, DecisionTree.queries, ih, List.map_cons,
      List.sum_cons, DecisionTree.eval]
    omega

theorem queries_seqList_le {γ δ : Type} (g : γ → DecisionTree ι Bool δ) (l : List γ)
    (x : ι → Bool) (K : ℕ) (h : ∀ c ∈ l, (g c).queries x ≤ K) :
    (seqList g l).queries x ≤ l.length * K := by
  rw [queries_seqList]
  have := List.sum_le_card_nsmul (l.map fun c => (g c).queries x) K
    (fun y hy => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hy
      exact h c hc)
  simpa using this

/-- Read the bits at positions `f 0, …, f (w-1)` and return their binary value. -/
def readNum {w : ℕ} (f : Fin w → ι) : DecisionTree ι Bool ℕ :=
  bindT (seqList (fun i => .node i fun b => .leaf b) (List.ofFn f))
    fun bs => .leaf (bitsVal fun t : Fin w => bs.getD t false)

theorem eval_readNum {w : ℕ} (f : Fin w → ι) (x : ι → Bool) :
    (readNum f).eval x = bitsVal fun t => x (f t) := by
  simp only [readNum, eval_bindT, eval_seqList, DecisionTree.eval]
  congr 1
  funext t
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem queries_readNum {w : ℕ} (f : Fin w → ι) (x : ι → Bool) :
    (readNum f).queries x = w := by
  simp only [readNum, queries_bindT, queries_seqList, DecisionTree.queries]
  simp [List.sum_ofFn]

end Generic

/-! ### Probability of a uniformly seeded algorithm -/

theorem successProb_uniform {ι σ : Type} [Fintype σ] [Nonempty σ]
    (tree : σ → DecisionTree ι Bool Bool) (x : ι → Bool) (b : Bool) :
    successProb ((PMF.uniformOfFintype σ).map tree) x b =
      ((Finset.univ.filter fun s => (tree s).eval x = b).card : ℝ) / Fintype.card σ := by
  classical
  unfold successProb
  rw [PMF.map_comp, PMF.map_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Function.comp_apply]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [div_eq_mul_inv]
  congr 3
  ext s
  simp [eq_comm]


/-! ### Encoding helpers -/

abbrev Ath (n : ℕ) := Fin (2 * n) × Fin n

theorem raceOf_val {n : ℕ} (c : Fin (2 * n)) (j : Fin (2 * n - 1)) :
    (raceOf c j).1 = if (j : ℕ) < c then (opponent c j, c) else (c, opponent c j) := by
  unfold raceOf
  split_ifs <;> rfl

theorem common_race_lt {n : ℕ} (c c' : Fin (2 * n)) (h : c < c') :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  have h1 : (c' : ℕ) < 2 * n := c'.isLt
  have h2 : (c : ℕ) < c' := h
  refine ⟨⟨c' - 1, by omega⟩, ⟨c, by omega⟩, ?_⟩
  have hA : ¬ ((c' : ℕ) - 1 < c) := by omega
  apply Subtype.ext
  simp only [raceOf, opponent, hA, h2, dif_neg, dif_pos, if_neg, if_pos, not_false_eq_true]
  ext
  · simp
  · simp; omega

theorem common_race {n : ℕ} (hn : 0 < n) (c c' : Fin (2 * n)) :
    ∃ j j' : Fin (2 * n - 1), raceOf c j = raceOf c' j' := by
  rcases lt_trichotomy c c' with h | h | h
  · exact common_race_lt c c' h
  · subst h
    exact ⟨⟨0, by omega⟩, ⟨0, by omega⟩, rfl⟩
  · obtain ⟨j, j', hj⟩ := common_race_lt c' c h
    exact ⟨j', j, hj.symm⟩

theorem athleteCode_injective (n : ℕ) (a a' : Ath n)
    (h : athleteCode n a = athleteCode n a') : a = a' := by
  unfold athleteCode at h
  have hb : (a.2 : ℕ) < n := a.2.isLt
  have hb' : (a'.2 : ℕ) < n := a'.2.isLt
  have h' : (a.1 : ℕ) * n + a.2 = (a'.1 : ℕ) * n + a'.2 := by omega
  have hc : (a.1 : ℕ) = a'.1 := by
    have e1 : ((a.1 : ℕ) * n + a.2) / n = a.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, zero_add]
    have e2 : ((a'.1 : ℕ) * n + a'.2) / n = a'.1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb', zero_add]
    rw [← e1, ← e2, h']
  have hb2 : (a.2 : ℕ) = a'.2 := by rw [hc] at h'; omega
  exact Prod.ext (Fin.ext hc) (Fin.ext hb2)

theorem athleteCode_pos (n : ℕ) (a : Ath n) : 0 < athleteCode n a := by
  unfold athleteCode; omega

def decode (n : ℕ) (v : ℕ) : Option (Ath n) :=
  if h : 1 ≤ v ∧ v ≤ 2 * n ^ 2 ∧ 0 < n then
    some (⟨(v - 1) / n, by
      rw [Nat.div_lt_iff_lt_mul h.2.2]
      have h1 := h.1; have h2 := h.2.1
      have h3 : 2 * n ^ 2 = 2 * n * n := by ring
      omega⟩, ⟨(v - 1) % n, Nat.mod_lt _ h.2.2⟩)
  else none

theorem decode_code {n : ℕ} (hn : 0 < n) (a : Ath n) : decode n (athleteCode n a) = some a := by
  have hb : (a.2 : ℕ) < n := a.2.isLt
  have hc : (a.1 : ℕ) < 2 * n := a.1.isLt
  have hle : athleteCode n a ≤ 2 * n ^ 2 := by unfold athleteCode; nlinarith
  unfold decode
  rw [dif_pos ⟨athleteCode_pos n a, hle, hn⟩]
  congr 1
  have hv : athleteCode n a - 1 = (a.1 : ℕ) * n + a.2 := by unfold athleteCode; omega
  apply Prod.ext
  · apply Fin.ext
    simp only [hv]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, zero_add]
  · apply Fin.ext
    simp only [hv]
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-! ### Reading entries -/

section Reads

variable (n : ℕ)

def readRace (r : Race n) (p : Fin n) : DecisionTree (Idx n) Bool ℕ :=
  readNum fun t : Fin (wX n) => (Sum.inl (r, p, t) : Idx n)

theorem eval_readRace (r : Race n) (p : Fin n) (x : Idx n → Bool) :
    (readRace n r p).eval x = raceEntry n x r p := by
  simp [readRace, eval_readNum, raceEntry]

theorem queries_readRace (r : Race n) (p : Fin n) (x : Idx n → Bool) :
    (readRace n r p).queries x = wX n := queries_readNum _ x

def readCard (a : Ath n) (j : Fin (2 * n - 1)) : DecisionTree (Idx n) Bool ℕ :=
  readNum fun t : Fin (wY n) => (Sum.inr (a, j, t) : Idx n)

theorem eval_readCard (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readCard n a j).eval x = cardEntry n x a j := by
  simp [readCard, eval_readNum, cardEntry]

theorem queries_readCard (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readCard n a j).queries x = wY n := queries_readNum _ x

def entryIf (x : Idx n → Bool) (r : Race n) (p : ℕ) : ℕ :=
  if h : p < n then raceEntry n x r ⟨p, h⟩ else 0

def readEntryIf (r : Race n) (p : ℕ) : DecisionTree (Idx n) Bool ℕ :=
  if h : p < n then readRace n r ⟨p, h⟩ else .leaf 0

theorem eval_readEntryIf (r : Race n) (p : ℕ) (x : Idx n → Bool) :
    (readEntryIf n r p).eval x = entryIf n x r p := by
  unfold readEntryIf entryIf
  split_ifs
  · exact eval_readRace n r _ x
  · rfl

theorem queries_readEntryIf (r : Race n) (p : ℕ) (x : Idx n → Bool) :
    (readEntryIf n r p).queries x ≤ wX n := by
  unfold readEntryIf
  split_ifs
  · exact (queries_readRace n r _ x).le
  · exact Nat.zero_le _

def readClaim (a : Ath n) (j : Fin (2 * n - 1)) : DecisionTree (Idx n) Bool ℕ :=
  bindT (readCard n a j) fun y1 =>
    if h : (j : ℕ) = 0 then .leaf (y1 - 0) else
      bindT (readCard n a ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩) fun y0 => .leaf (y1 - y0)

theorem eval_readClaim (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readClaim n a j).eval x = claimedPos n x a j := by
  unfold readClaim claimedPos
  rw [eval_bindT, eval_readCard]
  split_ifs with h
  · rfl
  · rw [eval_bindT, eval_readCard]; rfl

theorem queries_readClaim (a : Ath n) (j : Fin (2 * n - 1)) (x : Idx n → Bool) :
    (readClaim n a j).queries x ≤ 2 * wY n := by
  unfold readClaim
  rw [queries_bindT, queries_readCard]
  split_ifs with h
  · simp [DecisionTree.queries]; omega
  · rw [queries_bindT, queries_readCard]; simp [DecisionTree.queries]; omega

end Reads


/-! ### Comparing two potential champions -/


/-! ### Verifying a candidate -/

section Verify

variable (n : ℕ)

def posOf (Y : Fin (2 * n - 1) → ℕ) (j : Fin (2 * n - 1)) : ℕ :=
  Y j - (if h : (j : ℕ) = 0 then 0 else Y ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩)

theorem sum_posOf_lt (hn : 0 < n) (Y : Fin (2 * n - 1) → ℕ)
    (hmono : ∀ j j' : Fin (2 * n - 1), j ≤ j' → Y j ≤ Y j')
    (hlast : ∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → Y j < n) :
    ∑ j, posOf n Y j < n := by
  let F : ℕ → ℕ := fun k =>
    if k = 0 then 0 else Y ⟨min (k - 1) (2 * n - 2), by omega⟩
  have hFmono : Monotone F := by
    intro k k' hk
    simp only [F]
    split_ifs with h1 h2
    · exact le_rfl
    · exact Nat.zero_le _
    · omega
    · exact hmono _ _ (by simp only [Fin.le_def]; omega)
  have hpos : ∀ j : Fin (2 * n - 1), posOf n Y j = F (j + 1) - F j := by
    intro j
    have hj := j.isLt
    simp only [posOf, F]
    congr 1
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      congr 1
      ext
      simp only
      omega
    · by_cases h0 : (j : ℕ) = 0
      · simp [h0]
      · rw [dif_neg h0, if_neg h0]
        congr 1
        ext
        simp only
        omega
  have hsum : ∑ j, posOf n Y j = F (2 * n - 1) - F 0 := by
    simp only [hpos]
    rw [Fin.sum_univ_eq_sum_range (fun i => F (i + 1) - F i)]
    exact Finset.sum_range_tsub hFmono _
  rw [hsum]
  have hlastj := hlast ⟨2 * n - 2, by omega⟩ (by simp only; omega)
  have hF : F (2 * n - 1) = Y ⟨2 * n - 2, by omega⟩ := by
    simp only [F]
    rw [if_neg (by omega)]
    congr 1
    ext
    simp only
    omega
  rw [hF]
  simp only [F, if_pos]
  omega

def checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) : DecisionTree (Idx n) Bool Bool :=
  if p < n then
    bindT (seqList (fun m => bindT (readEntryIf n (raceOf a.1 j) m) fun e =>
        DecisionTree.leaf (decide (e = if m < p then 0 else athleteCode n a)))
      (List.range (p + 1))) fun bs => .leaf (bs.all id)
  else .leaf false

theorem eval_checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) (x : Idx n → Bool) :
    (checkRace n a j p).eval x = decide (p < n ∧ ∀ m < p + 1,
      entryIf n x (raceOf a.1 j) m = if m < p then 0 else athleteCode n a) := by
  unfold checkRace
  split_ifs with h
  · simp only [eval_bindT, eval_seqList, DecisionTree.eval, eval_readEntryIf]
    simp only [h, true_and]
    rw [Bool.eq_iff_iff, List.all_eq_true]
    simp [Nat.lt_succ_iff]
  · simp [DecisionTree.eval, h]

theorem queries_checkRace (a : Ath n) (j : Fin (2 * n - 1)) (p : ℕ) (x : Idx n → Bool) :
    (checkRace n a j p).queries x ≤ (p + 1) * wX n := by
  unfold checkRace
  split_ifs with h
  · rw [queries_bindT]
    simp only [DecisionTree.queries, add_zero]
    have := queries_seqList_le (fun m => bindT (readEntryIf n (raceOf a.1 j) m) fun e =>
        (DecisionTree.leaf (decide (e = if m < p then 0 else athleteCode n a)) :
          DecisionTree (Idx n) Bool Bool)) (List.range (p + 1)) x (wX n) (fun m _ => by
        rw [queries_bindT]
        simp only [DecisionTree.queries, add_zero]
        exact queries_readEntryIf n _ m x)
    simpa using this
  · simp [DecisionTree.queries]

def validCard (Ys : List ℕ) : Prop :=
  (∀ j j' : Fin (2 * n - 1), j ≤ j' → Ys.getD j 0 ≤ Ys.getD j' 0) ∧
    (∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → Ys.getD j 0 < n)

instance (Ys : List ℕ) : Decidable (validCard n Ys) := by unfold validCard; infer_instance

def verify (a : Ath n) : DecisionTree (Idx n) Bool Bool :=
  bindT (seqList (readCard n a) (List.finRange (2 * n - 1))) fun Ys =>
    if validCard n Ys then
      bindT (seqList (fun j => checkRace n a j (posOf n (fun j => Ys.getD j 0) j))
        (List.finRange (2 * n - 1))) fun bs => .leaf (bs.all id)
    else .leaf false

theorem getD_map_finRange {k : ℕ} (g : Fin k → ℕ) (j : Fin k) :
    ((List.finRange k).map g).getD j 0 = g j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem eval_verify (a : Ath n) (x : Idx n → Bool) :
    (verify n a).eval x = decide (IsChampion n x a) := by
  unfold verify
  rw [eval_bindT, eval_seqList]
  simp only [eval_readCard]
  have hY : ∀ j : Fin (2 * n - 1),
      ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j).getD j 0 = cardEntry n x a j :=
    getD_map_finRange _
  have hYf : (fun j : Fin (2 * n - 1) =>
      ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j).getD j 0) =
      fun j => cardEntry n x a j := funext hY
  have hvalid : validCard n ((List.finRange (2 * n - 1)).map fun j => cardEntry n x a j) ↔
      (∀ j j' : Fin (2 * n - 1), j ≤ j' → cardEntry n x a j ≤ cardEntry n x a j') ∧
        (∀ j : Fin (2 * n - 1), (j : ℕ) + 1 = 2 * n - 1 → cardEntry n x a j < n) := by
    unfold validCard
    simp only [hY]
  split_ifs with hv
  · rw [eval_bindT, eval_seqList]
    simp only [DecisionTree.eval, hYf, eval_checkRace]
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_map, List.mem_finRange, true_and, id_eq,
      forall_exists_index, forall_apply_eq_imp_iff, decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨(hvalid.1 hv).1, (hvalid.1 hv).2, fun j => ?_⟩
      obtain ⟨hlt, hall⟩ := h j
      have hcp : claimedPos n x a j = posOf n (fun j => cardEntry n x a j) j := rfl
      refine ⟨by rw [hcp]; exact hlt, fun q => ⟨fun hq => ?_, fun hq => ?_⟩⟩
      · have := hall q (by rw [hcp] at hq; omega)
        rw [if_pos (by rw [hcp] at hq; exact hq)] at this
        unfold entryIf at this
        rwa [dif_pos q.isLt] at this
      · have := hall q (by rw [hcp] at hq; omega)
        rw [if_neg (by rw [hcp] at hq; omega)] at this
        unfold entryIf at this
        rwa [dif_pos q.isLt] at this
    · intro hc j
      obtain ⟨hlt, hq⟩ := hc.2.2 j
      have hcp : claimedPos n x a j = posOf n (fun j => cardEntry n x a j) j := rfl
      rw [← hcp]
      refine ⟨hlt, fun m hm => ?_⟩
      unfold entryIf
      rw [dif_pos (by omega)]
      split_ifs with hmp
      · exact (hq ⟨m, by omega⟩).1 hmp
      · exact (hq ⟨m, by omega⟩).2 (by simp only; omega)
  · simp only [DecisionTree.eval]
    symm
    rw [decide_eq_false_iff_not]
    intro hc
    exact hv (hvalid.2 ⟨hc.1, hc.2.1⟩)

theorem queries_verify (hn : 0 < n) (a : Ath n) (x : Idx n → Bool) :
    (verify n a).queries x ≤ (2 * n - 1) * wY n + 3 * n * wX n := by
  unfold verify
  rw [queries_bindT]
  have h1 : (seqList (readCard n a) (List.finRange (2 * n - 1))).queries x ≤
      (2 * n - 1) * wY n := by
    have := queries_seqList_le (readCard n a) (List.finRange (2 * n - 1)) x (wY n)
      (fun j _ => (queries_readCard n a j x).le)
    simpa using this
  split_ifs with hv
  · rw [queries_bindT]
    simp only [DecisionTree.queries, add_zero]
    set Ys := (seqList (readCard n a) (List.finRange (2 * n - 1))).eval x
    have hsum := sum_posOf_lt n hn (fun j => Ys.getD j 0) hv.1 hv.2
    have h2 : (seqList (fun j => checkRace n a j (posOf n (fun j => Ys.getD j 0) j))
        (List.finRange (2 * n - 1))).queries x ≤ 3 * n * wX n := by
      rw [queries_seqList, ← Fin.sum_univ_def]
      calc ∑ j, (checkRace n a j (posOf n (fun j => Ys.getD j 0) j)).queries x
          ≤ ∑ j, (posOf n (fun j => Ys.getD j 0) j + 1) * wX n :=
            Finset.sum_le_sum fun j _ => queries_checkRace n a j _ x
        _ = (∑ j, posOf n (fun j => Ys.getD j 0) j + (2 * n - 1)) * wX n := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib]
            simp
        _ ≤ 3 * n * wX n := by
            apply Nat.mul_le_mul_right
            omega
    omega
  · simp only [DecisionTree.queries, add_zero]
    exact h1.trans (Nat.le_add_right _ _)

end Verify

/-! ### Queried positions of a decision tree -/

section Path

variable {ι : Type} [DecidableEq ι]

/-- The positions queried along the path that `x` follows. -/
def qset {α : Type} : DecisionTree ι Bool α → (ι → Bool) → Finset ι
  | .leaf _, _ => ∅
  | .node i next, x => insert i (qset (next (x i)) x)

theorem card_qset {α : Type} (t : DecisionTree ι Bool α) (x : ι → Bool) :
    (qset t x).card ≤ t.queries x := by
  induction t with
  | leaf a => simp [qset]
  | node i next ih =>
    simp only [qset, DecisionTree.queries]
    exact (Finset.card_insert_le _ _).trans (by have := ih (x i); omega)

theorem qset_agree {α : Type} (t : DecisionTree ι Bool α) (x y : ι → Bool)
    (h : ∀ i ∈ qset t x, y i = x i) : t.eval y = t.eval x ∧ qset t y = qset t x := by
  induction t with
  | leaf a => simp [qset, DecisionTree.eval]
  | node i next ih =>
    have hi : y i = x i := h i (by simp [qset])
    have h' : ∀ j ∈ qset (next (x i)) x, y j = x j := fun j hj => h j (by simp [qset, hj])
    simp only [qset, DecisionTree.eval, hi]
    obtain ⟨e1, e2⟩ := ih (x i) h'
    exact ⟨e1, by rw [e2]⟩

end Path

/-! ### The unambiguous cover -/

section Cover

variable (n : ℕ)

open Classical in
/-- The champion of a 1-input (an arbitrary athlete otherwise). -/
noncomputable def champOf (x : Idx n → Bool) (h : ∃ a, IsChampion n x a) : Ath n :=
  Classical.choose h

theorem champOf_spec (x : Idx n → Bool) (h : ∃ a, IsChampion n x a) :
    IsChampion n x (champOf n x h) := Classical.choose_spec h

/-- The partial assignment fixing exactly the bits that `verify a` reads on `x`. -/
def restr (a : Ath n) (x : Idx n → Bool) : Idx n → Option Bool :=
  fun i => if i ∈ qset (verify n a) x then some (x i) else none

open Classical in
noncomputable def rho (x : Idx n → Bool) : Idx n → Option Bool :=
  if h : ∃ a, IsChampion n x a then restr n (champOf n x h) x else fun _ => none

open Classical in
noncomputable def cover : Finset (Idx n → Option Bool) :=
  (Finset.univ.filter fun x : Idx n → Bool => champion n x = true).image (rho n)

theorem consistent_restr (a : Ath n) (x y : Idx n → Bool)
    (h : ∀ i b, restr n a x i = some b → y i = b) : ∀ i ∈ qset (verify n a) x, y i = x i := by
  intro i hi
  exact h i (x i) (by simp [restr, hi])

theorem champ_of_consistent (a : Ath n) (x y : Idx n → Bool) (ha : IsChampion n x a)
    (h : ∀ i b, restr n a x i = some b → y i = b) :
    IsChampion n y a ∧ restr n a y = restr n a x := by
  have hag := consistent_restr n a x y h
  obtain ⟨e1, e2⟩ := qset_agree (verify n a) x y hag
  rw [eval_verify, eval_verify] at e1
  refine ⟨by simpa [decide_eq_true ha] using e1, ?_⟩
  funext i
  unfold restr
  rw [e2]
  split_ifs with hi
  · rw [hag i hi]
  · rfl

theorem pos_of_champ {x : Idx n → Bool} {a : Ath n} (_ : IsChampion n x a) : 0 < n := by
  have := a.2.isLt; omega

theorem cover_unambiguous : IsUnambiguous1Cover (champion n) (cover n) := by
  classical
  constructor
  · intro ρ hρ y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
    have hx' : ∃ a, IsChampion n x a := of_decide_eq_true (Finset.mem_filter.1 hx).2
    have hy' : ∀ i b, restr n (champOf n x hx') x i = some b → y i = b := by
      intro i b hib; apply hy i b; simp only [rho, dif_pos hx']; exact hib
    exact decide_eq_true ⟨_, (champ_of_consistent n _ x y (champOf_spec n x hx') hy').1⟩
  · intro y hy
    have hy' : ∃ a, IsChampion n y a := of_decide_eq_true hy
    refine ⟨rho n y, ⟨Finset.mem_image.2 ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, rfl⟩,
      ?_⟩, ?_⟩
    · intro i b hib
      simp only [rho, dif_pos hy', restr] at hib
      split_ifs at hib
      exact Option.some.inj hib
    · rintro ρ ⟨hρ, hcons⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
      have hx' : ∃ a, IsChampion n x a := of_decide_eq_true (Finset.mem_filter.1 hx).2
      have hc : ∀ i b, restr n (champOf n x hx') x i = some b → y i = b := by
        intro i b hib; apply hcons i b; simp only [rho, dif_pos hx']; exact hib
      obtain ⟨hcy, hre⟩ := champ_of_consistent n _ x y (champOf_spec n x hx') hc
      have hn := pos_of_champ n hcy
      have heq : champOf n y hy' = champOf n x hx' :=
        lemma_2_unique n hn y _ _ (champOf_spec n y hy') hcy
      simp only [rho, dif_pos hy', dif_pos hx', heq]
      exact hre.symm

theorem cover_size (hn : 0 < n) : ∀ ρ ∈ cover n,
    (Finset.univ.filter fun i => (ρ i).isSome).card ≤ (2 * n - 1) * wY n + 3 * n * wX n := by
  classical
  intro ρ hρ
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
  have hx' : ∃ a, IsChampion n x a := of_decide_eq_true (Finset.mem_filter.1 hx).2
  have : (Finset.univ.filter fun i => (rho n x i).isSome) =
      qset (verify n (champOf n x hx')) x := by
    ext i; simp only [rho, dif_pos hx', restr, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with hi <;> simp [hi]
  rw [this]
  exact (card_qset _ x).trans (queries_verify n hn _ x)

end Cover

/-! ### `C1 ≤ UC1` for any function -/

theorem C1_le_UC1 {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool)
    (hne : {k : ℕ | ∃ P : Finset (ι → Option Bool), IsUnambiguous1Cover f P ∧
      ∀ ρ ∈ P, (Finset.univ.filter fun i => (ρ i).isSome).card ≤ k}.Nonempty) :
    C1 f ≤ UC1 f := by
  obtain ⟨P, hP, hsz⟩ := Nat.sInf_mem hne
  unfold C1
  apply Finset.sup_le
  intro x _
  split_ifs with hfx
  · obtain ⟨ρ, ⟨hρ, hcons⟩, -⟩ := hP.2 x hfx
    let S := Finset.univ.filter fun i => (ρ i).isSome
    have hcert : IsCertificate f x S := by
      intro y hy
      rw [hfx]
      apply hP.1 ρ hρ y
      intro i b hib
      have hiS : i ∈ S := by simp [S, hib]
      rw [hy i hiS]
      exact hcons i b hib
    have hc : certAt f x ≤ S.card := by
      unfold certAt
      exact Nat.sInf_le (show S.card ∈ {k : ℕ | ∃ T : Finset ι, IsCertificate f x T ∧ T.card = k}
        from ⟨S, hcert, rfl⟩)
    exact hc.trans (hsz ρ hρ)
  · exact Nat.zero_le _

end RvsCertL3

open RvsCertL3 in
theorem solution :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      C1 (champion n) ≤ UC1 (champion n) ∧
      (UC1 (champion n) : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) := by
  classical
  refine ⟨11, fun n hn => ?_⟩
  have hmem : (2 * n - 1) * wY n + 3 * n * wX n ∈ {k : ℕ | ∃ P : Finset (Idx n → Option Bool),
      IsUnambiguous1Cover (champion n) P ∧
      ∀ ρ ∈ P, (Finset.univ.filter fun i => (ρ i).isSome).card ≤ k} :=
    ⟨cover n, cover_unambiguous n, cover_size n hn⟩
  refine ⟨C1_le_UC1 _ ⟨_, hmem⟩, ?_⟩
  have hU : UC1 (champion n) ≤ (2 * n - 1) * wY n + 3 * n * wX n := Nat.sInf_le hmem
  have hY1 : 1 ≤ wY n := by unfold wY; omega
  have hX : wX n ≤ 2 * wY n + 1 := by
    apply Nat.clog_le_of_le_pow
    have h1 : n + 1 ≤ 2 ^ wY n := by
      unfold wY; exact Nat.lt_pow_succ_log_self (by norm_num) n
    have : 2 ^ (2 * wY n + 1) = 2 * (2 ^ wY n) ^ 2 := by ring
    rw [this]
    nlinarith
  have hT : UC1 (champion n) ≤ 11 * n * wY n := by
    have : (2 * n - 1) * wY n ≤ 2 * n * wY n := Nat.mul_le_mul_right _ (by omega)
    have : 3 * n * wX n ≤ 3 * n * (2 * wY n + 1) := Nat.mul_le_mul_left _ hX
    nlinarith
  have hlog : (wY n : ℝ) ≤ Real.logb 2 n + 1 := by
    unfold wY
    push_cast
    have := Real.natLog_le_logb n 2
    push_cast at this
    linarith
  have hT' : (UC1 (champion n) : ℝ) ≤ 11 * n * wY n := by exact_mod_cast hT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (UC1 (champion n) : ℝ) ≤ 11 * n * wY n := hT'
    _ ≤ 11 * n * (Real.logb 2 n + 1) := by gcongr

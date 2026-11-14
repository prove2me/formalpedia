-- Prove2me | solution 1 for RvsCert.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-13T21:18:04.584699+00:00
-- url     : https://prove2.me/submissions/0d2c5364-84d0-4133-9538-73589457090a

import Theorems.Thm_RvsCert_lemma_3_first_stage
import Definitions.Def_RvsCert_randQC
import Definitions.Def_RvsCert_champion

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

section Compare

variable (n : ℕ) (hn : 0 < n)

/-- Indices `(j, j')` of a common race: `raceOf p.1 j = raceOf q.1 j'`. -/
noncomputable def J (p q : Ath n) : Fin (2 * n - 1) × Fin (2 * n - 1) :=
  ((common_race hn p.1 q.1).choose, (common_race hn p.1 q.1).choose_spec.choose)

theorem J_spec (p q : Ath n) : raceOf p.1 (J n hn p q).1 = raceOf q.1 (J n hn p q).2 :=
  (common_race hn p.1 q.1).choose_spec.choose_spec

def winner (p q : Ath n) (pp pq ep eq : ℕ) : Ath n :=
  if pp < n ∧ ep = athleteCode n p then
    (if pq < n ∧ eq = athleteCode n q then (if pp ≤ pq then p else q) else p)
  else (if pq < n ∧ eq = athleteCode n q then q else p)

noncomputable def cmp (p q : Ath n) : DecisionTree (Idx n) Bool (Ath n) :=
  if p = q then .leaf p else
  bindT (readClaim n p (J n hn p q).1) fun pp =>
  bindT (readClaim n q (J n hn p q).2) fun pq =>
  bindT (readEntryIf n (raceOf p.1 (J n hn p q).1) pp) fun ep =>
  bindT (readEntryIf n (raceOf p.1 (J n hn p q).1) pq) fun eq =>
  .leaf (winner n p q pp pq ep eq)

theorem queries_cmp (p q : Ath n) (x : Idx n → Bool) :
    (cmp n hn p q).queries x ≤ 4 * wY n + 2 * wX n := by
  unfold cmp
  split_ifs
  · simp [DecisionTree.queries]
  · simp only [queries_bindT, eval_bindT, DecisionTree.queries]
    have := queries_readClaim n p (J n hn p q).1 x
    have := queries_readClaim n q (J n hn p q).2 x
    have := queries_readEntryIf n (raceOf p.1 (J n hn p q).1) ((readClaim n p (J n hn p q).1).eval x) x
    have := queries_readEntryIf n (raceOf p.1 (J n hn p q).1)
      ((readClaim n q (J n hn p q).2).eval x) x
    omega

theorem eval_cmp (p q : Ath n) (x : Idx n → Bool) (hpq : p ≠ q) :
    (cmp n hn p q).eval x =
      winner n p q (claimedPos n x p (J n hn p q).1) (claimedPos n x q (J n hn p q).2)
        (entryIf n x (raceOf p.1 (J n hn p q).1) (claimedPos n x p (J n hn p q).1))
        (entryIf n x (raceOf p.1 (J n hn p q).1) (claimedPos n x q (J n hn p q).2)) := by
  unfold cmp
  rw [if_neg hpq]
  simp only [eval_bindT, eval_readClaim, eval_readEntryIf, DecisionTree.eval]

/-- Facts about a champion's claim in its `j`-th race. -/
theorem champ_claim {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (j : Fin (2 * n - 1)) :
    claimedPos n x a j < n ∧
      entryIf n x (raceOf a.1 j) (claimedPos n x a j) = athleteCode n a ∧
      ∀ m < claimedPos n x a j, entryIf n x (raceOf a.1 j) m = 0 := by
  obtain ⟨hlt, hq⟩ := ha.2.2 j
  refine ⟨hlt, ?_, fun m hm => ?_⟩
  · unfold entryIf; rw [dif_pos hlt]; exact (hq ⟨_, hlt⟩).2 rfl
  · unfold entryIf; rw [dif_pos (by omega)]; exact (hq ⟨m, by omega⟩).1 hm

theorem entryIf_lt {x : Idx n → Bool} {r : Race n} {m : ℕ} (h : entryIf n x r m ≠ 0) : m < n := by
  unfold entryIf at h; split_ifs at h with hm; exact hm; exact absurd rfl h

theorem cmp_left {x : Idx n → Bool} {p : Ath n} (hp : IsChampion n x p) (q : Ath n) :
    (cmp n hn p q).eval x = p := by
  by_cases hpq : p = q
  · unfold cmp; rw [if_pos hpq]; rfl
  rw [eval_cmp n hn p q x hpq]
  obtain ⟨hlt, hcode, hzero⟩ := champ_claim n hp (J n hn p q).1
  unfold winner
  rw [if_pos ⟨hlt, hcode⟩]
  split_ifs with hq hle
  · rfl
  · exfalso
    have := hzero (claimedPos n x q (J n hn p q).2) (by omega)
    rw [hq.2] at this
    exact absurd this (athleteCode_pos n q).ne'
  · rfl

theorem cmp_right {x : Idx n → Bool} {q : Ath n} (hq : IsChampion n x q) (p : Ath n) :
    (cmp n hn p q).eval x = q := by
  by_cases hpq : p = q
  · unfold cmp; rw [if_pos hpq]; exact hpq
  rw [eval_cmp n hn p q x hpq]
  obtain ⟨hlt, hcode, hzero⟩ := champ_claim n hq (J n hn p q).2
  rw [← J_spec n hn p q] at hcode hzero
  unfold winner
  split_ifs with hp hq' hle hq''
  · exfalso
    rcases Nat.lt_or_ge (claimedPos n x p (J n hn p q).1) (claimedPos n x q (J n hn p q).2)
      with hlt' | hge
    · have := hzero _ hlt'
      rw [hp.2] at this
      exact absurd this (athleteCode_pos n p).ne'
    · have heq : claimedPos n x p (J n hn p q).1 = claimedPos n x q (J n hn p q).2 := by omega
      have h2 := hp.2
      rw [heq, hcode] at h2
      exact hpq (athleteCode_injective n p q h2.symm)
  · rfl
  · exact absurd ⟨hlt, hcode⟩ hq'
  · rfl
  · exact absurd ⟨hlt, hcode⟩ hq''

end Compare

/-! ### Knockout over the candidate list -/

section Knock

variable (n : ℕ) (hn : 0 < n)

noncomputable def step (cur : Option (Ath n)) (v : ℕ) : DecisionTree (Idx n) Bool (Option (Ath n)) :=
  match decode n v, cur with
  | none, _ => .leaf cur
  | some q, none => .leaf (some q)
  | some q, some p => bindT (cmp n hn p q) fun w => .leaf (some w)

noncomputable def knock : Option (Ath n) → List ℕ → DecisionTree (Idx n) Bool (Option (Ath n))
  | cur, [] => .leaf cur
  | cur, v :: l => bindT (step n hn cur v) fun c' => knock c' l

theorem queries_step (cur : Option (Ath n)) (v : ℕ) (x : Idx n → Bool) :
    (step n hn cur v).queries x ≤ 4 * wY n + 2 * wX n := by
  unfold step
  rcases decode n v with _ | q <;> rcases cur with _ | p <;>
    simp only [DecisionTree.queries, Nat.zero_le]
  rw [queries_bindT]
  simp only [DecisionTree.queries, add_zero]
  exact queries_cmp n hn p q x

theorem queries_knock (l : List ℕ) (x : Idx n → Bool) :
    ∀ cur, (knock n hn cur l).queries x ≤ l.length * (4 * wY n + 2 * wX n) := by
  induction l with
  | nil => intro cur; simp [knock, DecisionTree.queries]
  | cons v l ih =>
    intro cur
    simp only [knock, queries_bindT, List.length_cons]
    have := queries_step n hn cur v x
    have := ih ((step n hn cur v).eval x)
    nlinarith

theorem step_keep {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (v : ℕ) :
    (step n hn (some a) v).eval x = some a := by
  unfold step
  rcases decode n v with _ | q
  · rfl
  · simp only [eval_bindT, DecisionTree.eval, cmp_left n hn ha q]

theorem step_hit {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (cur : Option (Ath n))
    (v : ℕ) (hv : decode n v = some a) : (step n hn cur v).eval x = some a := by
  unfold step
  rw [hv]
  rcases cur with _ | p
  · rfl
  · simp only [eval_bindT, DecisionTree.eval, cmp_right n hn ha p]

theorem knock_champ {x : Idx n → Bool} {a : Ath n} (ha : IsChampion n x a) (l : List ℕ) :
    ∀ cur, (cur = some a ∨ ∃ v ∈ l, decode n v = some a) → (knock n hn cur l).eval x = some a := by
  induction l with
  | nil =>
    intro cur h
    rcases h with h | ⟨v, hv, -⟩
    · exact h
    · simp at hv
  | cons v l ih =>
    intro cur h
    simp only [knock, eval_bindT]
    apply ih
    rcases h with h | ⟨w, hw, hdec⟩
    · left; rw [h]; exact step_keep n hn ha v
    · rcases List.mem_cons.1 hw with rfl | hw'
      · left; exact step_hit n hn ha cur w hdec
      · by_cases hd : decode n v = some a
        · left; exact step_hit n hn ha cur v hd
        · right; exact ⟨w, hw', hdec⟩

end Knock


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


/-! ### The full algorithm -/

section Main

variable (n : ℕ) (hn : 0 < n)

def pairs : List (Fin (2 * n) × Fin 2) :=
  (List.finRange (2 * n)).flatMap fun c => (List.finRange 2).map fun i => (c, i)

theorem mem_pairs (c : Fin (2 * n)) (i : Fin 2) : (c, i) ∈ pairs n := by
  simp [pairs]

theorem length_pairs : (pairs n).length = 4 * n := by
  simp [pairs, List.length_flatMap]
  ring

def cands (s : Fin 2 → Fin (2 * n - 1)) : DecisionTree (Idx n) Bool (List ℕ) :=
  seqList (fun ci : Fin (2 * n) × Fin 2 => readRace n (raceOf ci.1 (s ci.2)) ⟨0, hn⟩) (pairs n)

noncomputable def alg (s : Fin 2 → Fin (2 * n - 1)) : DecisionTree (Idx n) Bool Bool :=
  bindT (cands n hn s) fun cl => bindT (knock n hn none cl) fun o =>
    match o with
    | none => .leaf false
    | some a => verify n a

def Tbound : ℕ :=
  4 * n * wX n + 4 * n * (4 * wY n + 2 * wX n) + ((2 * n - 1) * wY n + 3 * n * wX n)

theorem queries_alg (s : Fin 2 → Fin (2 * n - 1)) (x : Idx n → Bool) :
    (alg n hn s).queries x ≤ Tbound n := by
  unfold alg Tbound
  rw [queries_bindT, queries_bindT]
  have h1 : (cands n hn s).queries x ≤ 4 * n * wX n := by
    have := queries_seqList_le (fun ci : Fin (2 * n) × Fin 2 =>
      readRace n (raceOf ci.1 (s ci.2)) ⟨0, hn⟩) (pairs n) x (wX n)
      (fun ci _ => (queries_readRace n _ _ x).le)
    rwa [length_pairs] at this
  have hlen : ((cands n hn s).eval x).length = 4 * n := by
    unfold cands; rw [eval_seqList, List.length_map, length_pairs]
  have h2 := queries_knock n hn ((cands n hn s).eval x) x none
  rw [hlen] at h2
  have h3 : (match (knock n hn none ((cands n hn s).eval x)).eval x with
      | none => (DecisionTree.leaf false : DecisionTree (Idx n) Bool Bool)
      | some a => verify n a).queries x ≤ (2 * n - 1) * wY n + 3 * n * wX n := by
    rcases (knock n hn none ((cands n hn s).eval x)).eval x with _ | a
    · simp [DecisionTree.queries]
    · exact queries_verify n hn a x
  omega

theorem alg_noChamp (x : Idx n → Bool) (h : ¬ ∃ a, IsChampion n x a)
    (s : Fin 2 → Fin (2 * n - 1)) : (alg n hn s).eval x = false := by
  unfold alg
  rw [eval_bindT, eval_bindT]
  rcases (knock n hn none ((cands n hn s).eval x)).eval x with _ | a
  · rfl
  · show (verify n a).eval x = false
    rw [eval_verify, decide_eq_false_iff_not]
    exact fun ha => h ⟨a, ha⟩

theorem alg_champ (x : Idx n → Bool) (a : Ath n) (ha : IsChampion n x a)
    (s : Fin 2 → Fin (2 * n - 1))
    (hs : ∃ i, raceEntry n x (raceOf a.1 (s i)) ⟨0, hn⟩ = athleteCode n a) :
    (alg n hn s).eval x = true := by
  obtain ⟨i, hi⟩ := hs
  unfold alg
  rw [eval_bindT, eval_bindT]
  have hk : (knock n hn none ((cands n hn s).eval x)).eval x = some a := by
    apply knock_champ n hn ha
    right
    refine ⟨athleteCode n a, ?_, decode_code hn a⟩
    unfold cands
    rw [eval_seqList]
    exact List.mem_map.2 ⟨(a.1, i), mem_pairs n a.1 i, by rw [eval_readRace]; exact hi⟩
  rw [hk]
  show (verify n a).eval x = true
  rw [eval_verify]
  exact decide_eq_true ha

end Main

end RvsCertL3

open RvsCertL3 in
theorem solution :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n → ∃ T : ℕ, randQC (champion n) ≤ T ∧
      (T : ℝ) ≤ A * (n : ℝ) * (Real.logb 2 n + 1) := by
  refine ⟨63, fun n hn => ⟨Tbound n, ?_, ?_⟩⟩
  · have : Nonempty (Fin (2 * n - 1)) := ⟨⟨0, by omega⟩⟩
    unfold randQC
    refine iInf₂_le (Tbound n)
      ⟨(PMF.uniformOfFintype (Fin 2 → Fin (2 * n - 1))).map (alg n hn), ?_, fun x => ?_⟩
    · intro t ht y
      rw [PMF.support_map] at ht
      obtain ⟨s, -, rfl⟩ := ht
      exact queries_alg n hn s y
    · rw [successProb_uniform]
      have hN : Fintype.card (Fin 2 → Fin (2 * n - 1)) = (2 * n - 1) ^ 2 := by simp
      rw [hN]
      have hNpos : (0 : ℝ) < ((2 * n - 1) ^ 2 : ℕ) := by
        have : 0 < (2 * n - 1) ^ 2 := pow_pos (by omega) 2
        exact_mod_cast this
      rw [le_div_iff₀ hNpos]
      by_cases hc : ∃ a, IsChampion n x a
      · obtain ⟨a, ha⟩ := hc
        have hfx : champion n x = true := decide_eq_true ⟨a, ha⟩
        rw [hfx]
        set W := Finset.univ.filter fun j : Fin (2 * n - 1) =>
          raceEntry n x (raceOf a.1 j) ⟨0, hn⟩ = athleteCode n a with hW
        have hWcard : 2 * W.card ≥ 2 * n - 1 := lemma_3_first_stage n hn x a ha
        have hbad : (Finset.univ.filter fun s : Fin 2 → Fin (2 * n - 1) => ∀ i, s i ∉ W).card =
            (2 * n - 1 - W.card) ^ 2 := by
          have : (Finset.univ.filter fun s : Fin 2 → Fin (2 * n - 1) => ∀ i, s i ∉ W) =
              Fintype.piFinset fun _ => Wᶜ := by
            ext s; simp [Fintype.mem_piFinset]
          rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_compl]
          simp
        have hsub : (Finset.univ.filter fun s : Fin 2 → Fin (2 * n - 1) => ¬ ∀ i, s i ∉ W) ⊆
            Finset.univ.filter fun s => (alg n hn s).eval x = true := by
          intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hs ⊢
          obtain ⟨i, hi⟩ := hs
          exact alg_champ n hn x a ha s ⟨i, (Finset.mem_filter.1 hi).2⟩
        have htot := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin 2 → Fin (2 * n - 1)))) fun s => ∀ i, s i ∉ W
        rw [Finset.card_univ, hN, hbad] at htot
        have hgood := Finset.card_le_card hsub
        have hWle : W.card ≤ 2 * n - 1 := by
          calc W.card ≤ (Finset.univ : Finset (Fin (2 * n - 1))).card := Finset.card_le_univ _
            _ = 2 * n - 1 := by simp
        have hk : 2 * n - 1 - W.card ≤ n - 1 := by omega
        have hsq : 3 * (2 * n - 1 - W.card) ^ 2 ≤ (2 * n - 1) ^ 2 := by
          have h1 : (2 * n - 1 - W.card) ^ 2 ≤ (n - 1) ^ 2 := Nat.pow_le_pow_left hk 2
          have h2 : 3 * (n - 1) ^ 2 ≤ (2 * n - 1) ^ 2 := by
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
            simp only [Nat.add_sub_cancel]
            have : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
            rw [this]
            nlinarith
          omega
        have hnat : 2 * (2 * n - 1) ^ 2 ≤
            3 * (Finset.univ.filter fun s => (alg n hn s).eval x = true).card := by omega
        have : (2 : ℝ) * ((2 * n - 1) ^ 2 : ℕ) ≤
            3 * ((Finset.univ.filter fun s => (alg n hn s).eval x = true).card : ℝ) := by
          exact_mod_cast hnat
        linarith
      · have hfx : champion n x = false := decide_eq_false hc
        rw [hfx]
        have : (Finset.univ.filter fun s : Fin 2 → Fin (2 * n - 1) =>
            (alg n hn s).eval x = false) = Finset.univ := by
          ext s; simp [alg_noChamp n hn x hc s]
        rw [this, Finset.card_univ, hN]
        have : (0 : ℝ) ≤ ((2 * n - 1) ^ 2 : ℕ) := Nat.cast_nonneg _
        linarith
  · -- the numerical bound
    have hY1 : 1 ≤ wY n := by unfold wY; omega
    have hX : wX n ≤ 2 * wY n + 1 := by
      apply Nat.clog_le_of_le_pow
      have h1 : n + 1 ≤ 2 ^ wY n := by
        unfold wY; exact Nat.lt_pow_succ_log_self (by norm_num) n
      have : 2 ^ (2 * wY n + 1) = 2 * (2 ^ wY n) ^ 2 := by ring
      rw [this]
      nlinarith
    have hT : Tbound n ≤ 63 * n * wY n := by
      unfold Tbound
      have : (2 * n - 1) * wY n ≤ 2 * n * wY n := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    have hlog : (wY n : ℝ) ≤ Real.logb 2 n + 1 := by
      unfold wY
      push_cast
      have := Real.natLog_le_logb n 2
      push_cast at this
      linarith
    have hT' : (Tbound n : ℝ) ≤ 63 * n * wY n := by exact_mod_cast hT
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc (Tbound n : ℝ) ≤ 63 * n * wY n := hT'
      _ ≤ 63 * n * (Real.logb 2 n + 1) := by gcongr

-- Prove2me | solution 1 for QuantumLTF.Membership.Supplement.theorem_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-24T01:20:16.3608+00:00
-- url     : https://prove2.me/submissions/9f61c5b7-7deb-4593-8eb5-9efa5179db3f

import Mathlib
import Definitions.Def_QuantumLTF_Membership_QueryTree
import Definitions.Def_QuantumLTF_Membership_Supplement_majJunta
import Definitions.Def_QuantumLTF_Membership_Supplement_IsBooleanTree

open QuantumLTF.Membership QuantumLTF.Membership.Supplement Filter

namespace Aux_w_a1

/-- Boolean vector in `ℝⁿ` encoding a subset `S : Finset (Fin n)` with `+1` on `S` and `-1` outside. -/
noncomputable def boolVec {n : ℕ} (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => if i ∈ S then (1 : ℝ) else -1

/-- The oracle function passed to `QueryTree.run` for target `A`. -/
noncomputable def evalMaj {n : ℕ} (A : Finset (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℤ :=
  open Classical in
  majJunta A (Finset.univ.filter fun i => x i = 1)

lemma boolVec_isBoolean {n : ℕ} (S : Finset (Fin n)) :
    ∀ i : Fin n, boolVec S i = 1 ∨ boolVec S i = -1 := by
  intro i
  by_cases hi : i ∈ S <;> simp [boolVec, hi]

lemma filter_boolVec {n : ℕ} (S : Finset (Fin n)) :
    (open Classical in Finset.univ.filter fun i : Fin n => boolVec S i = 1) = S := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, boolVec]
  by_cases hi : i ∈ S <;> simp [hi]; norm_num

lemma evalMaj_boolVec {n : ℕ} (A S : Finset (Fin n)) :
    evalMaj A (boolVec S) = majJunta A S := by
  simp only [evalMaj]
  rw [filter_boolVec]

lemma majJunta_eq_one_or_neg_one {n : ℕ} (A S : Finset (Fin n)) :
    majJunta A S = 1 ∨ majJunta A S = -1 := by
  unfold majJunta
  split_ifs <;> simp

/-- Query a subset `S` and branch on `1` (`onYes`) vs `-1` (`onNo`). -/
noncomputable def querySubset {n : ℕ} {α : Type} (S : Finset (Fin n))
    (onYes onNo : QueryTree n α) : QueryTree n α :=
  .query (boolVec S) (fun ans => if ans = 1 then onYes else onNo)

lemma isBooleanTree_querySubset {n : ℕ} {α : Type} {S : Finset (Fin n)}
    {onYes onNo : QueryTree n α} (hY : IsBooleanTree onYes) (hN : IsBooleanTree onNo) :
    IsBooleanTree (querySubset S onYes onNo) := by
  refine ⟨boolVec_isBoolean S, ?_, ?_⟩
  · simpa using hY
  · simp [hN]

lemma depth_querySubset {n : ℕ} {α : Type} (S : Finset (Fin n))
    (onYes onNo : QueryTree n α) :
    (querySubset S onYes onNo).depth = 1 + max onYes.depth onNo.depth := by
  simp [querySubset, QueryTree.depth]

lemma run_querySubset {n : ℕ} {α : Type} (A S : Finset (Fin n))
    (onYes onNo : QueryTree n α) :
    (querySubset S onYes onNo).run (evalMaj A) =
      if majJunta A S = 1 then onYes.run (evalMaj A) else onNo.run (evalMaj A) := by
  by_cases h : majJunta A S = 1 <;> simp [querySubset, QueryTree.run, evalMaj_boolVec, h]

/-- Sequential composition of query trees. -/
def bindTree {n : ℕ} {α β : Type} : QueryTree n α → (α → QueryTree n β) → QueryTree n β
  | .leaf a, k => k a
  | .query x next, k => .query x (fun z => bindTree (next z) k)

lemma isBooleanTree_bindTree {n : ℕ} {α β : Type} {t : QueryTree n α}
    {k : α → QueryTree n β} (ht : IsBooleanTree t) (hk : ∀ a, IsBooleanTree (k a)) :
    IsBooleanTree (bindTree t k) := by
  induction t with
  | leaf a => exact hk a
  | query x next ih =>
    rcases ht with ⟨hx, h1, h2⟩
    exact ⟨hx, ih 1 h1, ih (-1) h2⟩

lemma depth_bindTree {n : ℕ} {α β : Type} (t : QueryTree n α)
    (k : α → QueryTree n β) {D : ℕ} (hk : ∀ a, (k a).depth ≤ D) :
    (bindTree t k).depth ≤ t.depth + D := by
  induction t with
  | leaf a =>
    simpa [bindTree, QueryTree.depth] using hk a
  | query x next ih =>
    simp only [bindTree, QueryTree.depth]
    have h1 := ih 1
    have h2 := ih (-1)
    omega

lemma run_bindTree {n : ℕ} {α β : Type} (t : QueryTree n α)
    (k : α → QueryTree n β) (f : EuclideanSpace ℝ (Fin n) → ℤ) :
    (bindTree t k).run f = (k (t.run f)).run f := by
  induction t with
  | leaf a => rfl
  | query x next ih =>
    simp only [bindTree, QueryTree.run]
    exact ih (f x)

/-- Prefix `{i : Fin n | i < j}`. -/
def prefixSet (n j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i : ℕ) < j)

/-- Binary search for the transition index `lo ≤ j < hi` from `-1` to `+1` on prefixes. -/
noncomputable def binSearchPrefix (n lo hi : ℕ) : QueryTree n ℕ :=
  if h : hi - lo ≤ 1 then
    .leaf lo
  else
    let mid := (lo + hi) / 2
    querySubset (prefixSet n mid)
      (binSearchPrefix n lo mid)
      (binSearchPrefix n mid hi)
termination_by hi - lo
decreasing_by all_goals omega

lemma isBooleanTree_binSearchPrefix (n lo hi : ℕ) :
    IsBooleanTree (binSearchPrefix n lo hi) := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d → IsBooleanTree (binSearchPrefix n lo hi) from
    h (hi - lo) lo hi rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd
    unfold binSearchPrefix
    split_ifs with h1
    · simp [IsBooleanTree]
    · apply isBooleanTree_querySubset
      · exact ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
      · exact ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl

lemma clog2_step {d : ℕ} (hd : 2 ≤ d) :
    1 + Nat.clog 2 ((d + 1) / 2) ≤ Nat.clog 2 d := by
  have hpow : d ≤ 2 ^ Nat.clog 2 d := Nat.le_pow_clog (by norm_num) d
  have hclog_pos : 1 ≤ Nat.clog 2 d := by
    by_contra h0
    have hzero : Nat.clog 2 d = 0 := by omega
    rw [hzero, pow_zero] at hpow
    omega
  have hpow2 : (d + 1) / 2 ≤ 2 ^ (Nat.clog 2 d - 1) := by
    have hsplit : 2 ^ Nat.clog 2 d = 2 * 2 ^ (Nat.clog 2 d - 1) := by
      conv_lhs => rw [show Nat.clog 2 d = (Nat.clog 2 d - 1) + 1 by omega]
      rw [pow_succ']
    omega
  have hle : Nat.clog 2 ((d + 1) / 2) ≤ Nat.clog 2 d - 1 :=
    (Nat.clog_le_iff_le_pow (by norm_num)).mpr hpow2
  omega

lemma depth_binSearchPrefix (n lo hi : ℕ) :
    (binSearchPrefix n lo hi).depth ≤ Nat.clog 2 (hi - lo) := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d →
      (binSearchPrefix n lo hi).depth ≤ Nat.clog 2 (hi - lo) from
    h (hi - lo) lo hi rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd
    unfold binSearchPrefix
    split_ifs with h1
    · simp [QueryTree.depth]
    · rw [depth_querySubset]
      set mid := (lo + hi) / 2
      have ih1 := ih (mid - lo) (by omega) lo mid rfl
      have ih2 := ih (hi - mid) (by omega) mid hi rfl
      have h1' : mid - lo ≤ (hi - lo + 1) / 2 := by omega
      have h2' : hi - mid ≤ (hi - lo + 1) / 2 := by omega
      have hc1 := le_trans ih1 (Nat.clog_mono_right 2 h1')
      have hc2 := le_trans ih2 (Nat.clog_mono_right 2 h2')
      have hstep := clog2_step (d := hi - lo) (by omega)
      omega

lemma run_binSearchPrefix {n : ℕ} (A : Finset (Fin n)) (lo hi : ℕ)
    (hlohi : lo < hi)
    (hlo : majJunta A (prefixSet n lo) = -1)
    (hhi : majJunta A (prefixSet n hi) = 1) :
    let x := (binSearchPrefix n lo hi).run (evalMaj A)
    lo ≤ x ∧ x < hi ∧ majJunta A (prefixSet n x) = -1 ∧
      majJunta A (prefixSet n (x + 1)) = 1 := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d → lo < hi →
      majJunta A (prefixSet n lo) = -1 → majJunta A (prefixSet n hi) = 1 →
      let x := (binSearchPrefix n lo hi).run (evalMaj A)
      lo ≤ x ∧ x < hi ∧ majJunta A (prefixSet n x) = -1 ∧
        majJunta A (prefixSet n (x + 1)) = 1 from
    h (hi - lo) lo hi rfl hlohi hlo hhi
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd hlohi hlo hhi
    unfold binSearchPrefix
    split_ifs with h1
    · have hhi_eq : hi = lo + 1 := by omega
      subst hhi_eq
      simp only [QueryTree.run]
      exact ⟨le_rfl, Nat.lt_succ_self lo, hlo, hhi⟩
    · rw [run_querySubset]
      set mid := (lo + hi) / 2
      have hlomid : lo < mid := by omega
      have hmidhi : mid < hi := by omega
      by_cases hmid : majJunta A (prefixSet n mid) = 1
      · simp only [hmid, ↓reduceIte]
        rcases ih (mid - lo) (by omega) lo mid rfl hlomid hlo hmid with ⟨hx1, hx2, hx3, hx4⟩
        exact ⟨hx1, lt_trans hx2 hmidhi, hx3, hx4⟩
      · simp only [hmid, ↓reduceIte]
        have hmid_neg : majJunta A (prefixSet n mid) = -1 := by
          rcases majJunta_eq_one_or_neg_one A (prefixSet n mid) with hpos | hneg
          · exact absurd hpos hmid
          · exact hneg
        rcases ih (hi - mid) (by omega) mid hi rfl hmidhi hmid_neg hhi with ⟨hx1, hx2, hx3, hx4⟩
        exact ⟨le_trans (le_of_lt hlomid) hx1, hx2, hx3, hx4⟩

def leftSet (n : ℕ) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => i < p)

def rightSet (n : ℕ) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => p < i)

def ivSet (n lo hi : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => lo ≤ (i : ℕ) ∧ (i : ℕ) < hi)

def MedianProp {n : ℕ} (A : Finset (Fin n)) (p : Fin n) : Prop :=
  p ∈ A ∧ 2 * (A ∩ leftSet n p).card < A.card ∧ A.card ≤ 2 * ((A ∩ leftSet n p).card + 1)

lemma medianProp_of_binSearch {n : ℕ} (hn : 1 ≤ n) (A : Finset (Fin n)) (hA : 1 ≤ A.card) :
    let pNat := (binSearchPrefix n 0 n).run (evalMaj A)
    ∃ hp : pNat < n, MedianProp A ⟨pNat, hp⟩ := by
  have h0 : majJunta A (prefixSet n 0) = -1 := by
    have hpref0 : prefixSet n 0 = ∅ := by
      ext i
      simp [prefixSet]
    rw [hpref0]
    simp only [majJunta, Finset.inter_empty, Finset.card_empty, mul_zero]
    split_ifs with hle
    · omega
    · rfl
  have hn1 : majJunta A (prefixSet n n) = 1 := by
    have hprefn : prefixSet n n = Finset.univ := by
      ext i
      simp [prefixSet]
    rw [hprefn]
    simp only [majJunta, Finset.inter_univ]
    split_ifs with hle
    · rfl
    · omega
  have hres := run_binSearchPrefix A 0 n hn h0 hn1
  dsimp only at hres
  rcases hres with ⟨_, hp_lt, hneg, hpos⟩
  refine ⟨hp_lt, ?_⟩
  let p : Fin n := ⟨(binSearchPrefix n 0 n).run (evalMaj A), hp_lt⟩
  have hL : prefixSet n p.1 = leftSet n p := by
    ext i
    simp only [prefixSet, leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  have hLp : prefixSet n (p.1 + 1) = insert p (leftSet n p) := by
    ext i
    simp only [prefixSet, leftSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Fin.ext_iff, Fin.lt_def]
    omega
  rw [hL] at hneg
  rw [hLp] at hpos
  have hlt : 2 * (A ∩ leftSet n p).card < A.card := by
    by_contra hc
    have hc' : A.card ≤ 2 * (A ∩ leftSet n p).card := by omega
    simp [majJunta, hc'] at hneg
  have hle : A.card ≤ 2 * (A ∩ insert p (leftSet n p)).card := by
    by_contra hc
    simp [majJunta, hc] at hpos
  have hpA : p ∈ A := by
    by_contra hp_not
    have heq : A ∩ insert p (leftSet n p) = A ∩ leftSet n p := by
      ext i
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hiA, rfl | hiL⟩
        · exact absurd hiA hp_not
        · exact ⟨hiA, hiL⟩
      · rintro ⟨hiA, hiL⟩
        exact ⟨hiA, Or.inr hiL⟩
    rw [heq] at hle
    omega
  have hp_not_L : p ∉ leftSet n p := by
    simp [leftSet]
  have hinter : A ∩ insert p (leftSet n p) = insert p (A ∩ leftSet n p) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨hiA, rfl | hiL⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hiA, hiL⟩
    · rintro (rfl | ⟨hiA, hiL⟩)
      · exact ⟨hpA, Or.inl rfl⟩
      · exact ⟨hiA, Or.inr hiL⟩
  have hp_not_inter : p ∉ A ∩ leftSet n p := fun h => hp_not_L (Finset.mem_inter.mp h).2
  have hcard : (A ∩ insert p (leftSet n p)).card = (A ∩ leftSet n p).card + 1 := by
    rw [hinter, Finset.card_insert_of_notMem hp_not_inter]
  rw [hcard] at hle
  exact ⟨hpA, hlt, hle⟩

def sideOk {n : ℕ} (p : Fin n) (side : Bool) (lo hi : ℕ) : Prop :=
  hi ≤ n ∧ if side then p.1 + 1 ≤ lo else hi ≤ p.1

lemma ivSet_subset_rightSet {n : ℕ} {p : Fin n} {lo hi : ℕ} (h : p.1 + 1 ≤ lo) :
    ivSet n lo hi ⊆ rightSet n p := by
  intro i hi_mem
  simp only [ivSet, rightSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi_mem ⊢
  omega

lemma ivSet_subset_leftSet {n : ℕ} {p : Fin n} {lo hi : ℕ} (h : hi ≤ p.1) :
    ivSet n lo hi ⊆ leftSet n p := by
  intro i hi_mem
  simp only [ivSet, leftSet, Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hi_mem ⊢
  omega

lemma majJunta_right_or {n : ℕ} {A Q : Finset (Fin n)} {p : Fin n}
    (hmed : MedianProp A p) (hQ : Q ⊆ rightSet n p) :
    majJunta A (leftSet n p ∪ Q) = 1 ↔ (A ∩ Q).Nonempty := by
  rcases hmed with ⟨_, hlt, hle⟩
  have hdisj : Disjoint (A ∩ leftSet n p) (A ∩ Q) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have hL : i < p := (Finset.mem_filter.mp (Finset.mem_inter.mp hi1).2).2
    have hR : p < i := (Finset.mem_filter.mp (hQ (Finset.mem_inter.mp hi2).2)).2
    exact lt_asymm hL hR
  have hunion : A ∩ (leftSet n p ∪ Q) = (A ∩ leftSet n p) ∪ (A ∩ Q) :=
    Finset.inter_union_distrib_left A _ _
  have hcard : (A ∩ (leftSet n p ∪ Q)).card = (A ∩ leftSet n p).card + (A ∩ Q).card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  unfold majJunta
  rw [hcard]
  by_cases hne : (A ∩ Q).Nonempty
  · have hc : 1 ≤ (A ∩ Q).card := Finset.Nonempty.card_pos hne
    have hcond : A.card ≤ 2 * ((A ∩ leftSet n p).card + (A ∩ Q).card) := by omega
    simp [hcond, hne]
  · have hc : (A ∩ Q).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hcond : ¬ A.card ≤ 2 * ((A ∩ leftSet n p).card + (A ∩ Q).card) := by omega
    simp only [hcond, ↓reduceIte, hne, iff_false]
    norm_num

lemma majJunta_left_or {n : ℕ} {A Q : Finset (Fin n)} {p : Fin n}
    (hmed : MedianProp A p) (hQ : Q ⊆ leftSet n p) :
    majJunta A ((leftSet n p \ Q) ∪ {p}) = 1 ↔ ¬ (A ∩ Q).Nonempty := by
  rcases hmed with ⟨hpA, hlt, hle⟩
  have hp_not_L : p ∉ leftSet n p := by simp [leftSet]
  have hinter : A ∩ ((leftSet n p \ Q) ∪ {p}) = insert p ((A ∩ leftSet n p) \ (A ∩ Q)) := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · rintro ⟨hiA, ⟨hiL, hiQ⟩ | rfl⟩
      · exact Or.inr ⟨⟨hiA, hiL⟩, fun h => hiQ h.2⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨⟨hiA, hiL⟩, hiQ⟩)
      · exact ⟨hpA, Or.inr rfl⟩
      · exact ⟨hiA, Or.inl ⟨hiL, fun h => hiQ ⟨hiA, h⟩⟩⟩
  have hp_not_rhs : p ∉ (A ∩ leftSet n p) \ (A ∩ Q) :=
    fun h => hp_not_L (Finset.mem_inter.mp (Finset.mem_sdiff.mp h).1).2
  have hsub : A ∩ Q ⊆ A ∩ leftSet n p := Finset.inter_subset_inter_left hQ
  have hcard : (A ∩ ((leftSet n p \ Q) ∪ {p})).card =
      ((A ∩ leftSet n p).card - (A ∩ Q).card) + 1 := by
    rw [hinter, Finset.card_insert_of_notMem hp_not_rhs, Finset.card_sdiff_of_subset hsub]
  have hAQ_le : (A ∩ Q).card ≤ (A ∩ leftSet n p).card := Finset.card_le_card hsub
  unfold majJunta
  rw [hcard]
  by_cases hne : (A ∩ Q).Nonempty
  · have hc : 1 ≤ (A ∩ Q).card := Finset.Nonempty.card_pos hne
    have hcond : ¬ A.card ≤ 2 * (((A ∩ leftSet n p).card - (A ∩ Q).card) + 1) := by omega
    simp only [hcond, ↓reduceIte, hne, not_true_eq_false, iff_false]
    norm_num
  · have hc : (A ∩ Q).card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    have hcond : A.card ≤ 2 * (((A ∩ leftSet n p).card - (A ∩ Q).card) + 1) := by omega
    simp [hcond, hne]

/-- Simulated OR-query on `ivSet n lo hi`. -/
noncomputable def queryOR {n : ℕ} {α : Type} (p : Fin n) (side : Bool) (lo hi : ℕ)
    (onNonempty onEmpty : QueryTree n α) : QueryTree n α :=
  if side then
    querySubset (leftSet n p ∪ ivSet n lo hi) onNonempty onEmpty
  else
    querySubset ((leftSet n p \ ivSet n lo hi) ∪ {p}) onEmpty onNonempty

lemma isBooleanTree_queryOR {n : ℕ} {α : Type} {p : Fin n} {side : Bool} {lo hi : ℕ}
    {onNonempty onEmpty : QueryTree n α}
    (h1 : IsBooleanTree onNonempty) (h2 : IsBooleanTree onEmpty) :
    IsBooleanTree (queryOR p side lo hi onNonempty onEmpty) := by
  by_cases hs : side <;> simp [queryOR, hs, isBooleanTree_querySubset h1 h2, isBooleanTree_querySubset h2 h1]

lemma depth_queryOR {n : ℕ} {α : Type} (p : Fin n) (side : Bool) (lo hi : ℕ)
    (onNonempty onEmpty : QueryTree n α) :
    (queryOR p side lo hi onNonempty onEmpty).depth =
      1 + max onNonempty.depth onEmpty.depth := by
  by_cases hs : side
  · simp [queryOR, hs, depth_querySubset]
  · simp [queryOR, hs, depth_querySubset, max_comm]

lemma run_queryOR {n : ℕ} {α : Type} {A : Finset (Fin n)} {p : Fin n}
    {side : Bool} {lo hi : ℕ}
    (hmed : MedianProp A p) (hsok : sideOk p side lo hi)
    (onNonempty onEmpty : QueryTree n α) :
    (queryOR p side lo hi onNonempty onEmpty).run (evalMaj A) =
      if (A ∩ ivSet n lo hi).Nonempty then onNonempty.run (evalMaj A) else onEmpty.run (evalMaj A) := by
  by_cases hs : side
  · simp only [sideOk, hs, ↓reduceIte] at hsok
    simp only [queryOR, hs, ↓reduceIte]
    rw [run_querySubset]
    by_cases hne : (A ∩ ivSet n lo hi).Nonempty
    · have hmaj : majJunta A (leftSet n p ∪ ivSet n lo hi) = 1 :=
        (majJunta_right_or hmed (ivSet_subset_rightSet hsok.2)).mpr hne
      rw [if_pos hmaj, if_pos hne]
    · have hmaj : majJunta A (leftSet n p ∪ ivSet n lo hi) ≠ 1 := by
        rw [ne_eq, majJunta_right_or hmed (ivSet_subset_rightSet (hi := hi) hsok.2)]
        exact hne
      rw [if_neg hmaj, if_neg hne]
  · simp only [sideOk, hs, Bool.false_eq_true, ↓reduceIte] at hsok
    simp only [queryOR, hs, Bool.false_eq_true, ↓reduceIte]
    rw [run_querySubset]
    by_cases hne : (A ∩ ivSet n lo hi).Nonempty
    · have hmaj : majJunta A ((leftSet n p \ ivSet n lo hi) ∪ {p}) ≠ 1 := by
        rw [ne_eq, majJunta_left_or hmed (ivSet_subset_leftSet (lo := lo) hsok.2)]
        exact not_not.mpr hne
      rw [if_neg hmaj, if_pos hne]
    · have hmaj : majJunta A ((leftSet n p \ ivSet n lo hi) ∪ {p}) = 1 :=
        (majJunta_left_or hmed (ivSet_subset_leftSet (lo := lo) hsok.2)).mpr hne
      rw [if_pos hmaj, if_neg hne]

/-- Binary search for the minimum element of `A` in `[lo, hi)`. -/
noncomputable def minInInterval (n : ℕ) (p : Fin n) (side : Bool) (lo hi : ℕ) : QueryTree n ℕ :=
  if h : hi - lo ≤ 1 then
    .leaf lo
  else
    let mid := (lo + hi) / 2
    queryOR p side lo mid
      (minInInterval n p side lo mid)
      (minInInterval n p side mid hi)
termination_by hi - lo
decreasing_by all_goals omega

lemma isBooleanTree_minInInterval (n : ℕ) (p : Fin n) (side : Bool) (lo hi : ℕ) :
    IsBooleanTree (minInInterval n p side lo hi) := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d → IsBooleanTree (minInInterval n p side lo hi) from
    h (hi - lo) lo hi rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd
    unfold minInInterval
    split_ifs with h1
    · simp [IsBooleanTree]
    · apply isBooleanTree_queryOR
      · exact ih ((lo + hi) / 2 - lo) (by omega) lo ((lo + hi) / 2) rfl
      · exact ih (hi - (lo + hi) / 2) (by omega) ((lo + hi) / 2) hi rfl

lemma depth_minInInterval (n : ℕ) (p : Fin n) (side : Bool) (lo hi : ℕ) :
    (minInInterval n p side lo hi).depth ≤ Nat.clog 2 (hi - lo) := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d →
      (minInInterval n p side lo hi).depth ≤ Nat.clog 2 (hi - lo) from
    h (hi - lo) lo hi rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd
    unfold minInInterval
    split_ifs with h1
    · simp [QueryTree.depth]
    · rw [depth_queryOR]
      set mid := (lo + hi) / 2
      have ih1 := ih (mid - lo) (by omega) lo mid rfl
      have ih2 := ih (hi - mid) (by omega) mid hi rfl
      have h1' : mid - lo ≤ (hi - lo + 1) / 2 := by omega
      have h2' : hi - mid ≤ (hi - lo + 1) / 2 := by omega
      have hc1 := le_trans ih1 (Nat.clog_mono_right 2 h1')
      have hc2 := le_trans ih2 (Nat.clog_mono_right 2 h2')
      have hstep := clog2_step (d := hi - lo) (by omega)
      omega

lemma run_minInInterval {n : ℕ} {A : Finset (Fin n)} {p : Fin n} {side : Bool} {lo hi : ℕ}
    (hmed : MedianProp A p) (hsok : sideOk p side lo hi)
    (hne : (A ∩ ivSet n lo hi).Nonempty) :
    let x := (minInInterval n p side lo hi).run (evalMaj A)
    lo ≤ x ∧ x < hi ∧ (∃ hx : x < n, ⟨x, hx⟩ ∈ A) ∧ A ∩ ivSet n lo x = ∅ := by
  suffices h : ∀ d lo hi : ℕ, hi - lo = d → sideOk p side lo hi →
      (A ∩ ivSet n lo hi).Nonempty →
      let x := (minInInterval n p side lo hi).run (evalMaj A)
      lo ≤ x ∧ x < hi ∧ (∃ hx : x < n, ⟨x, hx⟩ ∈ A) ∧ A ∩ ivSet n lo x = ∅ from
    h (hi - lo) lo hi rfl hsok hne
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro lo hi hd hsok hne
    unfold minInInterval
    split_ifs with h1
    · rcases hne with ⟨i, hi_mem⟩
      have hiA : i ∈ A := (Finset.mem_inter.mp hi_mem).1
      have hi_iv : lo ≤ i.1 ∧ i.1 < hi := (Finset.mem_filter.mp (Finset.mem_inter.mp hi_mem).2).2
      have hi_eq : i.1 = lo := by omega
      have hlo_lt_n : lo < n := by omega
      have hlo_in_A : ⟨lo, hlo_lt_n⟩ ∈ A := by
        have : (⟨lo, hlo_lt_n⟩ : Fin n) = i := Fin.ext hi_eq.symm
        rw [this]
        exact hiA
      have hempty : A ∩ ivSet n lo lo = ∅ := by
        ext j
        simp only [Finset.mem_inter, ivSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        omega
      simp only [QueryTree.run]
      exact ⟨le_rfl, by omega, ⟨hlo_lt_n, hlo_in_A⟩, hempty⟩
    · set mid := (lo + hi) / 2
      have hsok1 : sideOk p side lo mid := by
        rcases hsok with ⟨hhi, hside⟩
        refine ⟨by omega, ?_⟩
        by_cases hs : side <;> simp [hs] at hside ⊢ <;> omega
      have hsok2 : sideOk p side mid hi := by
        rcases hsok with ⟨hhi, hside⟩
        refine ⟨hhi, ?_⟩
        by_cases hs : side <;> simp [hs] at hside ⊢ <;> omega
      rw [run_queryOR hmed hsok1]
      by_cases hne1 : (A ∩ ivSet n lo mid).Nonempty
      · simp only [hne1, ↓reduceIte]
        rcases ih (mid - lo) (by omega) lo mid rfl hsok1 hne1 with ⟨hx1, hx2, hx3, hx4⟩
        exact ⟨hx1, by omega, hx3, hx4⟩
      · simp only [hne1, ↓reduceIte]
        have hne2 : (A ∩ ivSet n mid hi).Nonempty := by
          rcases hne with ⟨i, hi_mem⟩
          have hiA : i ∈ A := (Finset.mem_inter.mp hi_mem).1
          have hi_iv : lo ≤ i.1 ∧ i.1 < hi := (Finset.mem_filter.mp (Finset.mem_inter.mp hi_mem).2).2
          have hnot1 : ¬ (lo ≤ i.1 ∧ i.1 < mid) := fun h1' =>
            hne1 ⟨i, Finset.mem_inter.mpr ⟨hiA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩⟩⟩
          refine ⟨i, Finset.mem_inter.mpr ⟨hiA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩⟩
        rcases ih (hi - mid) (by omega) mid hi rfl hsok2 hne2 with ⟨hx1, hx2, hx3, hx4⟩
        refine ⟨by omega, hx2, hx3, ?_⟩
        ext j
        simp only [Finset.mem_inter, ivSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨hjA, hlo_j, hj_x⟩
        by_cases hjm : j.1 < mid
        · exact hne1 ⟨j, Finset.mem_inter.mpr ⟨hjA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo_j, hjm⟩⟩⟩
        · have hj_in : j ∈ A ∩ ivSet n mid ((minInInterval n p side mid hi).run (evalMaj A)) :=
            Finset.mem_inter.mpr ⟨hjA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hj_x⟩⟩
          rw [hx4] at hj_in
          exact Finset.notMem_empty _ hj_in

/-- Scan a list of intervals inside `L` and `R` with fuel `rem` for the remaining elements of `A`. -/
noncomputable def scanIntervals (n : ℕ) (p : Fin n)
    (intervals : List (Bool × ℕ × ℕ)) (rem : ℕ) (acc : Finset (Fin n)) :
    QueryTree n (Finset (Fin n)) :=
  match rem, intervals with
  | 0, _ => .leaf acc
  | _, [] => .leaf acc
  | rem' + 1, (side, lo, hi) :: rest =>
    if lo < hi then
      queryOR p side lo hi
        (bindTree (minInInterval n p side lo hi) fun x =>
          let acc' := if hx : x < n then insert ⟨x, hx⟩ acc else acc
          scanIntervals n p ((side, max (x + 1) (lo + 1), hi) :: rest) rem' acc')
        (scanIntervals n p rest (rem' + 1) acc)
    else
      scanIntervals n p rest (rem' + 1) acc
termination_by rem + intervals.length
decreasing_by all_goals (simp; try omega)

lemma isBooleanTree_scanIntervals (n : ℕ) (p : Fin n)
    (intervals : List (Bool × ℕ × ℕ)) (rem : ℕ) (acc : Finset (Fin n)) :
    IsBooleanTree (scanIntervals n p intervals rem acc) := by
  suffices h : ∀ m rem intervals acc, rem + intervals.length = m →
      IsBooleanTree (scanIntervals n p intervals rem acc) from
    h (rem + intervals.length) rem intervals acc rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro rem intervals acc hm
    cases rem with
    | zero => simp [scanIntervals, IsBooleanTree]
    | succ rem' =>
      cases intervals with
      | nil => simp [scanIntervals, IsBooleanTree]
      | cons head rest =>
        rcases head with ⟨side, lo, hi⟩
        unfold scanIntervals
        split_ifs with hlt
        · refine isBooleanTree_queryOR ?_ ?_
          · refine isBooleanTree_bindTree (isBooleanTree_minInInterval n p side lo hi) fun x => ?_
            exact ih (rem' + (rest.length + 1)) (by simp at hm; omega) rem' _ _ (by simp)
          · exact ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl
        · exact ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl

lemma depth_scanIntervals_zero (n : ℕ) (p : Fin n)
    (intervals : List (Bool × ℕ × ℕ)) (acc : Finset (Fin n)) :
    (scanIntervals n p intervals 0 acc).depth = 0 := by
  simp [scanIntervals, QueryTree.depth]

lemma depth_scanIntervals (n : ℕ) (p : Fin n) (w : ℕ)
    (intervals : List (Bool × ℕ × ℕ)) (rem : ℕ) (acc : Finset (Fin n))
    (hw : ∀ iv ∈ intervals, iv.2.2 - iv.2.1 ≤ w) :
    (scanIntervals n p intervals rem acc).depth ≤
      intervals.length + rem * (1 + Nat.clog 2 w) := by
  suffices h : ∀ m rem intervals acc, rem + intervals.length = m →
      (∀ iv ∈ intervals, iv.2.2 - iv.2.1 ≤ w) →
      (scanIntervals n p intervals rem acc).depth ≤
        intervals.length + rem * (1 + Nat.clog 2 w) from
    h (rem + intervals.length) rem intervals acc rfl hw
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro rem intervals acc hm hw
    cases rem with
    | zero => simp [scanIntervals, QueryTree.depth]
    | succ rem' =>
      cases intervals with
      | nil => simp [scanIntervals, QueryTree.depth]
      | cons head rest =>
        rcases head with ⟨side, lo, hi⟩
        have hw_head : hi - lo ≤ w := hw (side, lo, hi) List.mem_cons_self
        have hw_rest : ∀ iv ∈ rest, iv.2.2 - iv.2.1 ≤ w := fun iv hiv =>
          hw iv (List.mem_cons_of_mem _ hiv)
        unfold scanIntervals
        split_ifs with hlt
        · have h_empty := ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl hw_rest
          have h_cont : ∀ x : ℕ, (scanIntervals n p ((side, max (x + 1) (lo + 1), hi) :: rest) rem'
              (if hx : x < n then insert ⟨x, hx⟩ acc else acc)).depth ≤
              (rest.length + 1) + rem' * (1 + Nat.clog 2 w) := by
            intro x
            have hw' : ∀ iv ∈ ((side, max (x + 1) (lo + 1), hi) :: rest), iv.2.2 - iv.2.1 ≤ w := by
              intro iv hiv
              rcases List.mem_cons.mp hiv with rfl | hiv'
              · dsimp only
                omega
              · exact hw_rest iv hiv'
            simpa [List.length_cons] using
              ih (rem' + (rest.length + 1)) (by simp at hm; omega) rem' _ _ (by simp) hw'
          have h_bind : (bindTree (minInInterval n p side lo hi) fun x =>
              scanIntervals n p ((side, max (x + 1) (lo + 1), hi) :: rest) rem'
                (if hx : x < n then insert ⟨x, hx⟩ acc else acc)).depth ≤
              Nat.clog 2 w + ((rest.length + 1) + rem' * (1 + Nat.clog 2 w)) := by
            have hb := depth_bindTree (minInInterval n p side lo hi) _ h_cont
            have hm_clog := le_trans (depth_minInInterval n p side lo hi) (Nat.clog_mono_right 2 hw_head)
            omega
          rw [depth_queryOR]
          simp only [List.length_cons]
          have hmul : (rem' + 1) * (1 + Nat.clog 2 w) = rem' * (1 + Nat.clog 2 w) + (1 + Nat.clog 2 w) := by ring
          omega
        · have h_skip := ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl hw_rest
          simp only [List.length_cons]
          omega

def covered (n : ℕ) (intervals : List (Bool × ℕ × ℕ)) : Finset (Fin n) :=
  intervals.foldr (fun iv s => ivSet n iv.2.1 iv.2.2 ∪ s) ∅

lemma mem_covered {n : ℕ} {intervals : List (Bool × ℕ × ℕ)} {i : Fin n} :
    i ∈ covered n intervals ↔ ∃ iv ∈ intervals, i ∈ ivSet n iv.2.1 iv.2.2 := by
  induction intervals with
  | nil => simp [covered]
  | cons iv rest ih =>
    simp only [covered, List.foldr_cons, Finset.mem_union, List.mem_cons] at ih ⊢
    constructor
    · rintro (h | h)
      · exact ⟨iv, Or.inl rfl, h⟩
      · rcases ih.mp h with ⟨iv', hiv', hi⟩
        exact ⟨iv', Or.inr hiv', hi⟩
    · rintro ⟨iv', rfl | hiv', hi⟩
      · exact Or.inl hi
      · exact Or.inr (ih.mpr ⟨iv', hiv', hi⟩)

lemma run_scanIntervals {n : ℕ} {A : Finset (Fin n)} {p : Fin n}
    (hmed : MedianProp A p)
    (intervals : List (Bool × ℕ × ℕ)) (rem : ℕ) (acc : Finset (Fin n))
    (hsok : ∀ iv ∈ intervals, sideOk p iv.1 iv.2.1 iv.2.2)
    (hpw : List.Pairwise (fun u v => u.2.2 ≤ v.2.1) intervals)
    (hsub : acc ⊆ A)
    (hcov : A \ acc ⊆ covered n intervals)
    (hdisj : Disjoint acc (covered n intervals))
    (hrem : (A \ acc).card ≤ rem) :
    (scanIntervals n p intervals rem acc).run (evalMaj A) = A := by
  suffices h : ∀ m rem intervals acc, rem + intervals.length = m →
      (∀ iv ∈ intervals, sideOk p iv.1 iv.2.1 iv.2.2) →
      List.Pairwise (fun u v => u.2.2 ≤ v.2.1) intervals →
      acc ⊆ A →
      A \ acc ⊆ covered n intervals →
      Disjoint acc (covered n intervals) →
      (A \ acc).card ≤ rem →
      (scanIntervals n p intervals rem acc).run (evalMaj A) = A from
    h (rem + intervals.length) rem intervals acc rfl hsok hpw hsub hcov hdisj hrem
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro rem intervals acc hm hsok hpw hsub hcov hdisj hrem
    cases rem with
    | zero =>
      simp only [scanIntervals, QueryTree.run]
      have heq0 : (A \ acc).card = 0 := Nat.eq_zero_of_le_zero hrem
      have hsdiff : A \ acc = ∅ := Finset.card_eq_zero.mp heq0
      have hAsub : A ⊆ acc := Finset.sdiff_eq_empty_iff_subset.mp hsdiff
      exact Finset.Subset.antisymm hsub hAsub
    | succ rem' =>
      cases intervals with
      | nil =>
        simp only [scanIntervals, QueryTree.run]
        have hcov_empty : covered n [] = ∅ := rfl
        rw [hcov_empty] at hcov
        have hsdiff : A \ acc = ∅ := Finset.subset_empty.mp hcov
        have hAsub : A ⊆ acc := Finset.sdiff_eq_empty_iff_subset.mp hsdiff
        exact Finset.Subset.antisymm hsub hAsub
      | cons head rest =>
        rcases head with ⟨side, lo, hi⟩
        have hsok_head : sideOk p side lo hi := hsok (side, lo, hi) List.mem_cons_self
        have hsok_rest : ∀ iv ∈ rest, sideOk p iv.1 iv.2.1 iv.2.2 := fun iv hiv =>
          hsok iv (List.mem_cons_of_mem _ hiv)
        have hpw_cons := List.pairwise_cons.mp hpw
        have hpw_rest : List.Pairwise (fun u v => u.2.2 ≤ v.2.1) rest := hpw_cons.2
        unfold scanIntervals
        split_ifs with hlt
        · rw [run_queryOR hmed hsok_head]
          by_cases hne : (A ∩ ivSet n lo hi).Nonempty
          · simp only [hne, ↓reduceIte, run_bindTree]
            have hmin := run_minInInterval hmed hsok_head hne
            dsimp only at hmin
            rcases hmin with ⟨hlo_x, hx_hi, ⟨hx_n, hxA⟩, hempty_left⟩
            set x := (minInInterval n p side lo hi).run (evalMaj A)
            have hmax_eq : max (x + 1) (lo + 1) = x + 1 := by omega
            simp only [hx_n, ↓reduceDIte, hmax_eq]
            let xFin : Fin n := ⟨x, hx_n⟩
            have hsok' : ∀ iv ∈ ((side, x + 1, hi) :: rest), sideOk p iv.1 iv.2.1 iv.2.2 := by
              intro iv hiv
              rcases List.mem_cons.mp hiv with rfl | hiv'
              · rcases hsok_head with ⟨hhi, hside⟩
                refine ⟨hhi, ?_⟩
                by_cases hs : side <;> simp [hs] at hside ⊢ <;> omega
              · exact hsok_rest iv hiv'
            have hpw' : List.Pairwise (fun u v => u.2.2 ≤ v.2.1) ((side, x + 1, hi) :: rest) := by
              rw [List.pairwise_cons]
              exact ⟨hpw_cons.1, hpw_rest⟩
            have hsub' : insert xFin acc ⊆ A := Finset.insert_subset_iff.mpr ⟨hxA, hsub⟩
            have hcov' : A \ insert xFin acc ⊆ covered n ((side, x + 1, hi) :: rest) := by
              intro y hy
              rcases Finset.mem_sdiff.mp hy with ⟨hyA, hy_not⟩
              have hy_not_acc : y ∉ acc := fun h => hy_not (Finset.mem_insert_of_mem h)
              have hy_ne_x : y ≠ xFin := fun h => hy_not (h ▸ Finset.mem_insert_self xFin acc)
              have hy_cov := hcov (Finset.mem_sdiff.mpr ⟨hyA, hy_not_acc⟩)
              rw [mem_covered] at hy_cov ⊢
              rcases hy_cov with ⟨iv, hiv_mem, hy_iv⟩
              rcases List.mem_cons.mp hiv_mem with rfl | hiv
              · refine ⟨(side, x + 1, hi), List.mem_cons_self, ?_⟩
                simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy_iv ⊢
                have hy_not_lt : ¬ (y.1 < x) := by
                  intro hlt_x
                  have hmem : y ∈ A ∩ ivSet n lo x :=
                    Finset.mem_inter.mpr ⟨hyA, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_iv.1, hlt_x⟩⟩
                  rw [hempty_left] at hmem
                  exact Finset.notMem_empty _ hmem
                have hy_ne_val : y.1 ≠ x := fun heq => hy_ne_x (Fin.ext heq)
                omega
              · exact ⟨iv, List.mem_cons_of_mem _ hiv, hy_iv⟩
            have hdisj' : Disjoint (insert xFin acc) (covered n ((side, x + 1, hi) :: rest)) := by
              rw [Finset.disjoint_left]
              intro y hy_ins hy_cov
              rw [mem_covered] at hy_cov
              have hy_cov_orig : y ∈ covered n ((side, lo, hi) :: rest) := by
                rw [mem_covered]
                rcases hy_cov with ⟨iv, hiv_mem, hy_iv⟩
                rcases List.mem_cons.mp hiv_mem with rfl | hiv
                · refine ⟨(side, lo, hi), List.mem_cons_self, ?_⟩
                  simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy_iv ⊢
                  omega
                · exact ⟨iv, List.mem_cons_of_mem _ hiv, hy_iv⟩
              rcases Finset.mem_insert.mp hy_ins with rfl | hy_acc
              · rcases hy_cov with ⟨iv, hiv_mem, hy_iv⟩
                rcases List.mem_cons.mp hiv_mem with rfl | hiv
                · simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and, xFin] at hy_iv
                  omega
                · have hhi_iv : hi ≤ iv.2.1 := hpw_cons.1 iv hiv
                  simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and, xFin] at hy_iv
                  omega
              · exact Finset.disjoint_left.mp hdisj hy_acc hy_cov_orig
            have hx_cov : xFin ∈ covered n ((side, lo, hi) :: rest) := by
              rw [mem_covered]
              refine ⟨(side, lo, hi), List.mem_cons_self, ?_⟩
              simp [ivSet, xFin, hlo_x, hx_hi]
            have hx_not_acc : xFin ∉ acc := fun h => Finset.disjoint_left.mp hdisj h hx_cov
            have hcard' : (A \ insert xFin acc).card ≤ rem' := by
              have hsdiff_eq : A \ insert xFin acc = (A \ acc).erase xFin := by
                ext y
                simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
                tauto
              have hx_in_sdiff : xFin ∈ A \ acc := Finset.mem_sdiff.mpr ⟨hxA, hx_not_acc⟩
              rw [hsdiff_eq, Finset.card_erase_of_mem hx_in_sdiff]
              omega
            exact ih (rem' + (rest.length + 1)) (by simp at hm; omega) rem' _ _
              (by simp) hsok' hpw' hsub' hcov' hdisj' hcard'
          · simp only [hne, ↓reduceIte]
            have hcov' : A \ acc ⊆ covered n rest := by
              intro y hy
              rcases Finset.mem_sdiff.mp hy with ⟨hyA, _⟩
              have hy_cov := hcov hy
              rw [mem_covered] at hy_cov ⊢
              rcases hy_cov with ⟨iv, hiv_mem, hy_iv⟩
              rcases List.mem_cons.mp hiv_mem with rfl | hiv
              · exfalso
                exact hne ⟨y, Finset.mem_inter.mpr ⟨hyA, hy_iv⟩⟩
              · exact ⟨iv, hiv, hy_iv⟩
            have hdisj' : Disjoint acc (covered n rest) := by
              rw [Finset.disjoint_left]
              intro y hy_acc hy_cov
              rw [mem_covered] at hy_cov
              rcases hy_cov with ⟨iv, hiv, hy_iv⟩
              exact Finset.disjoint_left.mp hdisj hy_acc (mem_covered.mpr ⟨iv, List.mem_cons_of_mem _ hiv, hy_iv⟩)
            exact ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl
              hsok_rest hpw_rest hsub hcov' hdisj' hrem
        · have hiv_empty : ivSet n lo hi = ∅ := by
            ext y
            simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            omega
          have hcov' : A \ acc ⊆ covered n rest := by
            intro y hy
            have hy_cov := hcov hy
            rw [mem_covered] at hy_cov ⊢
            rcases hy_cov with ⟨iv, hiv_mem, hy_iv⟩
            rcases List.mem_cons.mp hiv_mem with rfl | hiv
            · rw [hiv_empty] at hy_iv
              exact absurd hy_iv (Finset.notMem_empty _)
            · exact ⟨iv, hiv, hy_iv⟩
          have hdisj' : Disjoint acc (covered n rest) := by
            rw [Finset.disjoint_left]
            intro y hy_acc hy_cov
            rw [mem_covered] at hy_cov
            rcases hy_cov with ⟨iv, hiv, hy_iv⟩
            exact Finset.disjoint_left.mp hdisj hy_acc (mem_covered.mpr ⟨iv, List.mem_cons_of_mem _ hiv, hy_iv⟩)
          exact ih (rem' + 1 + rest.length) (by simp at hm; omega) (rem' + 1) rest acc rfl
            hsok_rest hpw_rest hsub hcov' hdisj' hrem

/-- Partition `[a, b)` into contiguous subintervals of length at most `w`. -/
def chunkRange (side : Bool) (a b w : ℕ) : List (Bool × ℕ × ℕ) :=
  if _ : a < b ∧ 0 < w then
    let hi := min (a + w) b
    (side, a, hi) :: chunkRange side hi b w
  else []
termination_by b - a
decreasing_by omega

lemma chunkRange_mem {side : Bool} {a b w : ℕ} {iv : Bool × ℕ × ℕ}
    (hiv : iv ∈ chunkRange side a b w) :
    iv.1 = side ∧ a ≤ iv.2.1 ∧ iv.2.1 < iv.2.2 ∧ iv.2.2 ≤ b ∧ iv.2.2 - iv.2.1 ≤ w := by
  suffices h : ∀ d a, b - a = d → iv ∈ chunkRange side a b w →
      iv.1 = side ∧ a ≤ iv.2.1 ∧ iv.2.1 < iv.2.2 ∧ iv.2.2 ≤ b ∧ iv.2.2 - iv.2.1 ≤ w from
    h (b - a) a rfl hiv
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hd hiv
    unfold chunkRange at hiv
    split_ifs at hiv with h1
    · set hi := min (a + w) b
      rcases List.mem_cons.mp hiv with rfl | hiv'
      · dsimp only
        exact ⟨rfl, le_rfl, lt_min (by omega) h1.1, min_le_right _ _, by omega⟩
      · rcases ih (b - hi) (by omega) hi rfl hiv' with ⟨h1', h2', h3', h4', h5'⟩
        exact ⟨h1', le_trans (le_min (by omega) (le_of_lt h1.1)) h2', h3', h4', h5'⟩
    · simp at hiv

lemma chunkRange_pairwise (side : Bool) (a b w : ℕ) :
    List.Pairwise (fun u v => u.2.2 ≤ v.2.1) (chunkRange side a b w) := by
  suffices h : ∀ d a, b - a = d →
      List.Pairwise (fun u v => u.2.2 ≤ v.2.1) (chunkRange side a b w) from
    h (b - a) a rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hd
    unfold chunkRange
    split_ifs with h1
    · rw [List.pairwise_cons]
      refine ⟨fun v hv => ?_, ih (b - min (a + w) b) (by omega) (min (a + w) b) rfl⟩
      exact (chunkRange_mem hv).2.1
    · simp

lemma chunkRange_covers {side : Bool} {a b w i : ℕ} (hw : 0 < w) (ha : a ≤ i) (hb : i < b) :
    ∃ iv ∈ chunkRange side a b w, iv.2.1 ≤ i ∧ i < iv.2.2 := by
  suffices h : ∀ d a, b - a = d → a ≤ i → i < b →
      ∃ iv ∈ chunkRange side a b w, iv.2.1 ≤ i ∧ i < iv.2.2 from
    h (b - a) a rfl ha hb
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hd ha hb
    unfold chunkRange
    split_ifs with h1
    · let hi := min (a + w) b
      by_cases hlt : i < hi
      · exact ⟨(side, a, hi), List.mem_cons_self, ha, hlt⟩
      · rcases ih (b - hi) (by omega) hi rfl (by omega) hb with ⟨iv, hiv, h1', h2'⟩
        exact ⟨iv, List.mem_cons_of_mem _ hiv, h1', h2'⟩
    · exfalso
      exact h1 ⟨by omega, hw⟩

lemma chunkRange_length (side : Bool) (a b w : ℕ) (hw : 0 < w) :
    (chunkRange side a b w).length = (b - a + w - 1) / w := by
  suffices h : ∀ d a, b - a = d → (chunkRange side a b w).length = (b - a + w - 1) / w from
    h (b - a) a rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a hd
    unfold chunkRange
    split_ifs with h1
    · let hi := min (a + w) b
      simp only [List.length_cons]
      rw [ih (b - hi) (by omega) hi rfl]
      by_cases hle : b - a ≤ w
      · have hhi : hi = b := min_eq_right (by omega)
        rw [hhi]
        have hz : (b - b + w - 1) / w = 0 := by
          have : b - b + w - 1 = w - 1 := by omega
          rw [this]
          exact Nat.div_eq_of_lt (by omega)
        rw [hz]
        have hdiv : (b - a + w - 1) / w = 1 := by
          rw [show b - a + w - 1 = (b - a - 1) + 1 * w by omega, Nat.add_mul_div_right _ _ hw]
          have : (b - a - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
          omega
        omega
      · have hhi : hi = a + w := min_eq_left (by omega)
        rw [hhi]
        have hdiv : (b - a + w - 1) / w = (b - (a + w) + w - 1) / w + 1 := by
          rw [show b - a + w - 1 = (b - (a + w) + w - 1) + 1 * w by omega, Nat.add_mul_div_right _ _ hw]
        omega
    · have hba : b - a = 0 := by
        have : ¬ a < b := fun hab => h1 ⟨hab, hw⟩
        omega
      rw [hba]
      have : (0 + w - 1) / w = 0 := Nat.div_eq_of_lt (by omega)
      simp only [List.length_nil]
      omega

/-- Complete adaptive query tree learning `A` with `1 ≤ A.card ≤ k`. -/
noncomputable def learnMajTree (n k : ℕ) : QueryTree n (Finset (Fin n)) :=
  if _ : 1 ≤ n then
    bindTree (binSearchPrefix n 0 n) fun pNat =>
      if hp : pNat < n then
        let p : Fin n := ⟨pNat, hp⟩
        let w := (n + k - 1) / k
        let ivs := chunkRange false 0 p.1 w ++ chunkRange true (p.1 + 1) n w
        scanIntervals n p ivs (k - 1) {p}
      else
        .leaf ∅
  else
    .leaf ∅

lemma isBooleanTree_learnMajTree (n k : ℕ) :
    IsBooleanTree (learnMajTree n k) := by
  unfold learnMajTree
  split_ifs with hn
  · refine isBooleanTree_bindTree (isBooleanTree_binSearchPrefix n 0 n) fun pNat => ?_
    split_ifs with hp
    · exact isBooleanTree_scanIntervals n ⟨pNat, hp⟩ _ (k - 1) {⟨pNat, hp⟩}
    · simp [IsBooleanTree]
  · simp [IsBooleanTree]

lemma ivs_length_le {n k pNat : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hp : pNat < n) :
    let w := (n + k - 1) / k
    (chunkRange false 0 pNat w ++ chunkRange true (pNat + 1) n w).length ≤ k + 1 := by
  intro w
  have hw : 0 < w := by
    have : k ≤ n + k - 1 := by omega
    exact Nat.div_pos this (by omega)
  rw [List.length_append, chunkRange_length _ _ _ _ hw, chunkRange_length _ _ _ _ hw]
  set L1 := (pNat - 0 + w - 1) / w
  set L2 := (n - (pNat + 1) + w - 1) / w
  have h1 : L1 * w ≤ pNat + w - 1 := by
    simpa [L1] using Nat.div_mul_le_self (pNat - 0 + w - 1) w
  have h2 : L2 * w ≤ n - (pNat + 1) + w - 1 := by
    simpa [L2] using Nat.div_mul_le_self (n - (pNat + 1) + w - 1) w
  have hnw : n ≤ k * w := by
    have hmod : n + k - 1 = k * w + (n + k - 1) % k := by
      simpa [w] using (Nat.div_add_mod (n + k - 1) k).symm
    have hrem : (n + k - 1) % k < k := Nat.mod_lt _ (by omega)
    omega
  have hsum : (L1 + L2) * w < (k + 2) * w := by
    have hadd : (L1 + L2) * w = L1 * w + L2 * w := Nat.add_mul L1 L2 w
    have hkw_pos : 3 ≤ (k + 2) * w := by
      have : 3 ≤ k + 2 := by omega
      nlinarith
    have hmul : (k + 2) * w = k * w + 2 * w := Nat.add_mul k 2 w
    omega
  have hlt : L1 + L2 < k + 2 := Nat.lt_of_mul_lt_mul_right hsum
  omega

lemma run_learnMajTree {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : Finset (Fin n)) (hA1 : 1 ≤ A.card) (hAk : A.card ≤ k) :
    (learnMajTree n k).run (evalMaj A) = A := by
  have hn : 1 ≤ n := by omega
  simp only [learnMajTree, hn, ↓reduceDIte, run_bindTree]
  have hmed_ex := medianProp_of_binSearch hn A hA1
  dsimp only at hmed_ex
  rcases hmed_ex with ⟨hp, hmed⟩
  simp only [hp, ↓reduceDIte]
  let p : Fin n := ⟨(binSearchPrefix n 0 n).run (evalMaj A), hp⟩
  let w := (n + k - 1) / k
  let ivs := chunkRange false 0 p.1 w ++ chunkRange true (p.1 + 1) n w
  have hw : 0 < w := Nat.div_pos (by omega) (by omega)
  have hsok : ∀ iv ∈ ivs, sideOk p iv.1 iv.2.1 iv.2.2 := by
    intro iv hiv
    rcases List.mem_append.mp hiv with hiv | hiv
    · rcases chunkRange_mem hiv with ⟨h1, h2, h3, h4, _⟩
      refine ⟨by omega, ?_⟩
      simp [h1, h4]
    · rcases chunkRange_mem hiv with ⟨h1, h2, h3, h4, _⟩
      refine ⟨h4, ?_⟩
      simp [h1, h2]
  have hpw : List.Pairwise (fun u v => u.2.2 ≤ v.2.1) ivs := by
    rw [List.pairwise_append]
    refine ⟨chunkRange_pairwise false 0 p.1 w, chunkRange_pairwise true (p.1 + 1) n w, ?_⟩
    intro u hu v hv
    have hu4 := (chunkRange_mem hu).2.2.2.1
    have hv2 := (chunkRange_mem hv).2.1
    omega
  have hpA : p ∈ A := hmed.1
  have hsub : ({p} : Finset (Fin n)) ⊆ A := Finset.singleton_subset_iff.mpr hpA
  have hcov : A \ {p} ⊆ covered n ivs := by
    intro i hi
    rcases Finset.mem_sdiff.mp hi with ⟨_, hi_ne⟩
    have hi_ne' : i.1 ≠ p.1 := fun h => hi_ne (Finset.mem_singleton.mpr (Fin.ext h))
    rw [mem_covered]
    by_cases hlt : i.1 < p.1
    · rcases chunkRange_covers (side := false) hw (Nat.zero_le i.1) hlt with ⟨iv, hiv, h1, h2⟩
      exact ⟨iv, List.mem_append_left _ hiv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
    · have hgt : p.1 + 1 ≤ i.1 := by omega
      rcases chunkRange_covers (side := true) hw hgt i.isLt with ⟨iv, hiv, h1, h2⟩
      exact ⟨iv, List.mem_append_right _ hiv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩⟩
  have hdisj : Disjoint ({p} : Finset (Fin n)) (covered n ivs) := by
    rw [Finset.disjoint_left]
    intro i hi_p hi_cov
    have hi_eq : i = p := Finset.mem_singleton.mp hi_p
    subst hi_eq
    rw [mem_covered] at hi_cov
    rcases hi_cov with ⟨iv, hiv, hi_iv⟩
    simp only [ivSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi_iv
    rcases List.mem_append.mp hiv with hiv | hiv
    · have h4 := (chunkRange_mem hiv).2.2.2.1
      omega
    · have h2 := (chunkRange_mem hiv).2.1
      omega
  have hrem : (A \ {p}).card ≤ k - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hpA), Finset.card_singleton]
    omega
  exact run_scanIntervals hmed ivs (k - 1) {p} hsok hpw hsub hcov hdisj hrem

lemma half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hexp : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hlt4 : Real.exp (1 / 2 : ℝ) ^ 2 < 2 ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hlt4
  have hlog : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 :=
    Real.log_lt_log (Real.exp_pos _) hexp
  rwa [Real.log_exp] at hlog

lemma clog2_real_le {m : ℕ} (hm : 1 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ 1 + 2 * Real.log (m : ℝ) := by
  by_cases hm1 : m = 1
  · subst hm1
    simp
  · have hm2 : 2 ≤ m := by omega
    have hc1 : 1 ≤ Nat.clog 2 m := by
      by_contra h0
      have hz : Nat.clog 2 m = 0 := by omega
      have hpow : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
      rw [hz, pow_zero] at hpow
      omega
    have hlt_pow : 2 ^ (Nat.clog 2 m - 1) < m := by
      by_contra hle
      have hclog_le := (Nat.clog_le_iff_le_pow (by norm_num)).mpr (not_lt.mp hle)
      omega
    have hpow_real : ((2 : ℝ) ^ (Nat.clog 2 m - 1)) < (m : ℝ) := by exact_mod_cast hlt_pow
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 m - 1) := by positivity
    have hlog_lt : Real.log ((2 : ℝ) ^ (Nat.clog 2 m - 1)) < Real.log (m : ℝ) :=
      Real.log_lt_log hpow_pos hpow_real
    rw [Real.log_pow] at hlog_lt
    have hhalf := half_lt_log_two
    have hc_real : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
      rw [Nat.cast_sub hc1, Nat.cast_one]
    rw [hc_real] at hlog_lt
    nlinarith

lemma depth_learnMajTree_le {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ((learnMajTree n k).depth : ℝ) ≤ 8 * k * Real.log (Real.exp 1 * n / k) := by
  have hn : 1 ≤ n := by omega
  let w := (n + k - 1) / k
  have hw : 1 ≤ w := Nat.div_pos (by omega) (by omega)
  have hdepth_nat : (learnMajTree n k).depth ≤
      Nat.clog 2 n + (if k = 1 then 0 else (k + 1) + (k - 1) * (1 + Nat.clog 2 w)) := by
    simp only [learnMajTree, hn, ↓reduceDIte]
    refine le_trans (depth_bindTree (binSearchPrefix n 0 n) _
        (D := if k = 1 then 0 else (k + 1) + (k - 1) * (1 + Nat.clog 2 w)) ?_) ?_
    · intro pNat
      split_ifs with hp hk1
      · simp only [hk1, Nat.sub_self, depth_scanIntervals_zero, le_refl]
      · have hlen := ivs_length_le hk hkn hp
        have hw_ivs : ∀ iv ∈ chunkRange false 0 pNat w ++ chunkRange true (pNat + 1) n w,
            iv.2.2 - iv.2.1 ≤ w := by
          intro iv hiv
          rcases List.mem_append.mp hiv with hiv | hiv
          · exact (chunkRange_mem hiv).2.2.2.2
          · exact (chunkRange_mem hiv).2.2.2.2
        have hscan := depth_scanIntervals n ⟨pNat, hp⟩ w _ (k - 1) {⟨pNat, hp⟩} hw_ivs
        dsimp only [w] at hlen hscan ⊢
        omega
      · simp [QueryTree.depth]
      · simp [QueryTree.depth]
    · have hbs := depth_binSearchPrefix n 0 n
      simp only [Nat.sub_zero] at hbs
      omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnk_ge1 : (1 : ℝ) ≤ (n : ℝ) / k := (one_le_div hk_pos).mpr (by exact_mod_cast hkn)
  let L := Real.log (Real.exp 1 * n / k)
  have hL_eq : L = 1 + Real.log ((n : ℝ) / k) := by
    have hmul : Real.exp 1 * (n : ℝ) / k = Real.exp 1 * ((n : ℝ) / k) := by ring
    dsimp only [L]
    rw [hmul, Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp]
  have hlog_nk_nonneg : 0 ≤ Real.log ((n : ℝ) / k) := Real.log_nonneg hnk_ge1
  have hL_ge1 : 1 ≤ L := by linarith
  have hlog_n_le : Real.log (n : ℝ) ≤ (k : ℝ) * L := by
    have hnk_eq : (n : ℝ) = (k : ℝ) * ((n : ℝ) / k) := by field_simp
    rw [hnk_eq, Real.log_mul hk_pos.ne' (by positivity)]
    have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) := by
      linarith [Real.log_le_sub_one_of_pos hk_pos]
    have hlognk : Real.log ((n : ℝ) / k) ≤ (k : ℝ) * Real.log ((n : ℝ) / k) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    rw [hL_eq]
    nlinarith
  have hclog_n : (Nat.clog 2 n : ℝ) ≤ 3 * (k : ℝ) * L := by
    have h1 := clog2_real_le hn
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have h1kL : (1 : ℝ) ≤ (k : ℝ) * L := by nlinarith
    linarith
  have hdepth_real : ((learnMajTree n k).depth : ℝ) ≤ 8 * (k : ℝ) * L := by
    by_cases hk1 : k = 1
    · have hd : ((learnMajTree n k).depth : ℝ) ≤ (Nat.clog 2 n : ℝ) := by
        have hnat : (learnMajTree n k).depth ≤ Nat.clog 2 n := by simpa [hk1] using hdepth_nat
        exact_mod_cast hnat
      have h38 : 3 * (k : ℝ) * L ≤ 8 * (k : ℝ) * L := by nlinarith
      linarith
    · have hk2 : 2 ≤ k := by omega
      have hw_real : (w : ℝ) ≤ 2 * ((n : ℝ) / k) := by
        have hdiv : (w : ℝ) ≤ ((n + k - 1 : ℕ) : ℝ) / k := by
          rw [le_div_iff₀ hk_pos]
          exact_mod_cast Nat.div_mul_le_self (n + k - 1) k
        have hnum : ((n + k - 1 : ℕ) : ℝ) ≤ (n : ℝ) + k := by
          have : n + k - 1 ≤ n + k := by omega
          exact_mod_cast this
        have hnum_div : ((n + k - 1 : ℕ) : ℝ) / k ≤ (n : ℝ) / k + 1 := by
          rw [div_le_iff₀ hk_pos]
          have : ((n : ℝ) / k + 1) * k = (n : ℝ) + k := by field_simp
          linarith
        linarith
      have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
      have hlog_w : Real.log (w : ℝ) ≤ L := by
        have h1 : Real.log (w : ℝ) ≤ Real.log (2 * ((n : ℝ) / k)) :=
          Real.log_le_log hw_pos hw_real
        have h2 : Real.log (2 * ((n : ℝ) / k)) = Real.log 2 + Real.log ((n : ℝ) / k) :=
          Real.log_mul (by norm_num) (by positivity)
        have hlog2 : Real.log 2 ≤ 1 := by
          have hexp2 : (2 : ℝ) ≤ Real.exp 1 := by
            linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
          have hlt := Real.log_le_log (by norm_num) hexp2
          rwa [Real.log_exp] at hlt
        linarith
      have hclog_w : (Nat.clog 2 w : ℝ) ≤ 3 * L := by
        have h1 := clog2_real_le hw
        linarith
      have hnat_real : ((learnMajTree n k).depth : ℝ) ≤
          (Nat.clog 2 n : ℝ) + ((k : ℝ) + 1) + ((k : ℝ) - 1) * (1 + (Nat.clog 2 w : ℝ)) := by
        have hnat : (learnMajTree n k).depth ≤
            Nat.clog 2 n + ((k + 1) + (k - 1) * (1 + Nat.clog 2 w)) := by
          simpa [hk1] using hdepth_nat
        have hcast : ((Nat.clog 2 n + ((k + 1) + (k - 1) * (1 + Nat.clog 2 w)) : ℕ) : ℝ) =
            (Nat.clog 2 n : ℝ) + ((k : ℝ) + 1) + ((k : ℝ) - 1) * (1 + (Nat.clog 2 w : ℝ)) := by
          have hk_ge1 : 1 ≤ k := hk
          push_cast [Nat.cast_sub hk_ge1]
          ring
        exact le_trans (by exact_mod_cast hnat) (le_of_eq hcast)
      have hk1_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hrest : ((k : ℝ) + 1) + ((k : ℝ) - 1) * (1 + (Nat.clog 2 w : ℝ)) ≤
          2 * (k : ℝ) * L + 3 * (k : ℝ) * L := by
        have ha : ((k : ℝ) + 1) + ((k : ℝ) - 1) ≤ 2 * (k : ℝ) := by linarith
        have hb : 2 * (k : ℝ) ≤ 2 * (k : ℝ) * L := by nlinarith
        have hc : ((k : ℝ) - 1) * (Nat.clog 2 w : ℝ) ≤ (k : ℝ) * (3 * L) := by
          have hcw_nonneg : (0 : ℝ) ≤ (Nat.clog 2 w : ℝ) := by positivity
          nlinarith
        nlinarith
      linarith
  exact hdepth_real

end Aux_w_a1

theorem solution :
    (∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      ∃ t : QueryTree n (Finset (Fin n)), IsBooleanTree t ∧
        (t.depth : ℝ) ≤ C * k * Real.log (Real.exp 1 * n / k) ∧
        ∀ A : Finset (Fin n), 1 ≤ A.card → A.card ≤ k →
          open Classical in
          t.run (fun x => majJunta A (Finset.univ.filter fun i => x i = 1)) = A) ∧
    ∀ nk : ℕ → ℕ, (∃ ρ : ℝ, 1 < ρ ∧ ∀ᶠ k in atTop, ρ ≤ (nk k : ℝ) / k) →
      ∃ C' : ℝ, 0 < C' ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∃ t : QueryTree (nk k) (Finset (Fin (nk k))), IsBooleanTree t ∧
          (t.depth : ℝ) ≤ C' * k * Real.log ((nk k : ℝ) / k) ∧
          ∀ A : Finset (Fin (nk k)), 1 ≤ A.card → A.card ≤ k →
            open Classical in
            t.run (fun x => majJunta A (Finset.univ.filter fun i => x i = 1)) = A := by
  have hpart1 : ∃ C : ℝ, 0 < C ∧ ∀ n k : ℕ, 1 ≤ k → k ≤ n →
      ∃ t : QueryTree n (Finset (Fin n)), IsBooleanTree t ∧
        (t.depth : ℝ) ≤ C * k * Real.log (Real.exp 1 * n / k) ∧
        ∀ A : Finset (Fin n), 1 ≤ A.card → A.card ≤ k →
          open Classical in
          t.run (fun x => majJunta A (Finset.univ.filter fun i => x i = 1)) = A := by
    refine ⟨8, by norm_num, fun n k hk hkn => ?_⟩
    refine ⟨Aux_w_a1.learnMajTree n k, Aux_w_a1.isBooleanTree_learnMajTree n k,
      Aux_w_a1.depth_learnMajTree_le hk hkn, fun A hA1 hAk => ?_⟩
    exact Aux_w_a1.run_learnMajTree hk hkn A hA1 hAk
  refine ⟨hpart1, ?_⟩
  rcases hpart1 with ⟨C, hC_pos, hbound⟩
  rintro nk ⟨ρ, hρ, hev⟩
  rw [Filter.eventually_atTop] at hev
  rcases hev with ⟨k₁, hk₁⟩
  have hlog_ρ_pos : 0 < Real.log ρ := Real.log_pos hρ
  let C' := C * (1 + 1 / Real.log ρ)
  have hC'_pos : 0 < C' := by positivity
  refine ⟨C', hC'_pos, max 1 k₁, fun k hk => ?_⟩
  have hk_ge1 : 1 ≤ k := le_trans (le_max_left 1 k₁) hk
  have hk_gek1 : k₁ ≤ k := le_trans (le_max_right 1 k₁) hk
  have hρ_le : ρ ≤ (nk k : ℝ) / k := hk₁ k hk_gek1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_ge1
  have hnk_gt_k : (k : ℝ) < (nk k : ℝ) := by
    have : 1 < (nk k : ℝ) / k := lt_of_lt_of_le hρ hρ_le
    exact (one_lt_div hk_pos).mp this
  have hkn : k ≤ nk k := by
    have : (k : ℝ) ≤ (nk k : ℝ) := le_of_lt hnk_gt_k
    exact_mod_cast this
  rcases hbound (nk k) k hk_ge1 hkn with ⟨t, ht_bool, ht_depth, ht_run⟩
  refine ⟨t, ht_bool, ?_, ht_run⟩
  have hlog_ge : Real.log ρ ≤ Real.log ((nk k : ℝ) / k) :=
    Real.log_le_log (by linarith) hρ_le
  have hlog_nk_pos : 0 < Real.log ((nk k : ℝ) / k) := lt_of_lt_of_le hlog_ρ_pos hlog_ge
  have h1_le : 1 ≤ (1 / Real.log ρ) * Real.log ((nk k : ℝ) / k) := by
    rw [one_div_mul_eq_div]
    exact (one_le_div hlog_ρ_pos).mpr hlog_ge
  have hnk_div_pos : 0 < (nk k : ℝ) / k := by linarith
  have hlog_exp : Real.log (Real.exp 1 * (nk k : ℝ) / k) = 1 + Real.log ((nk k : ℝ) / k) := by
    have hmul : Real.exp 1 * (nk k : ℝ) / k = Real.exp 1 * ((nk k : ℝ) / k) := by ring
    rw [hmul, Real.log_mul (Real.exp_ne_zero 1) hnk_div_pos.ne', Real.log_exp]
  have hlog_cmp : Real.log (Real.exp 1 * (nk k : ℝ) / k) ≤
      (1 + 1 / Real.log ρ) * Real.log ((nk k : ℝ) / k) := by
    rw [hlog_exp]
    linarith
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
  calc
    (t.depth : ℝ) ≤ C * k * Real.log (Real.exp 1 * (nk k : ℝ) / k) := ht_depth
    _ ≤ C * k * ((1 + 1 / Real.log ρ) * Real.log ((nk k : ℝ) / k)) := by
        apply mul_le_mul_of_nonneg_left hlog_cmp
        exact mul_nonneg (le_of_lt hC_pos) hk_nonneg
    _ = C' * k * Real.log ((nk k : ℝ) / k) := by
        dsimp only [C']
        ring

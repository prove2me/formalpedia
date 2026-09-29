-- Prove2me | solution 1 for Rudin.ch06_upper_lower_integral_additive
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T14:49:37.802957+00:00
-- url     : https://prove2.me/submissions/9933686f-c866-4c9a-b19b-68972980e63a

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_ch06_refinement
import Theorems.Thm_Rudin_ch06_lower_le_upper

open Filter Topology

namespace RudinAdd

open Rudin

/-- A generic sum over the subintervals of a partition. -/
noncomputable def psum {a b : ℝ} (g : ℝ → ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ i ∈ Finset.range P.n, g (P.x i) (P.x (i + 1))

lemma upperSum_eq_psum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) :
    upperSum f α P = psum (fun u v => sSup (f '' Set.Icc u v) * (α v - α u)) P := rfl

lemma lowerSum_eq_psum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) :
    lowerSum f α P = psum (fun u v => sInf (f '' Set.Icc u v) * (α v - α u)) P := rfl

/-- The division points of a partition increase. -/
lemma px_mono {a b : ℝ} (P : Partition a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ P.n) :
    P.x i ≤ P.x j := by
  induction j with
  | zero =>
    have : i = 0 := Nat.le_zero.mp hij
    simp [this]
  | succ m ih =>
    rcases Nat.lt_or_ge i (m + 1) with h | h
    · have him : i ≤ m := Nat.lt_succ_iff.mp h
      exact le_trans (ih him (by omega)) (P.mono m (by omega))
    · have : i = m + 1 := le_antisymm hij h
      simp [this]

lemma px_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have := px_mono P (Nat.zero_le i) hi
    rwa [P.first] at this
  · have := px_mono P hi (le_refl P.n)
    rwa [P.last] at this

/-- Merge a partition of `[a, c]` with one of `[c, b]`. -/
def merge {a c b : ℝ} (P₁ : Partition a c) (P₂ : Partition c b) : Partition a b where
  n := P₁.n + P₂.n
  x := fun j => if j ≤ P₁.n then P₁.x j else P₂.x (j - P₁.n)
  first := by simpa using P₁.first
  last := by
    rcases Nat.eq_zero_or_pos P₂.n with h | h
    · have hcb : c = b := by
        have h1 := P₂.first
        have h2 := P₂.last
        rw [h] at h2
        rw [h1] at h2
        exact h2
      simp only [h, Nat.add_zero, le_refl, if_pos]
      rw [P₁.last, hcb]
    · have hlt : ¬ (P₁.n + P₂.n ≤ P₁.n) := by omega
      simp only [hlt, if_false]
      simpa using P₂.last
  mono := by
    intro j hj
    rcases lt_trichotomy j P₁.n with h | h | h
    · have h1 : j ≤ P₁.n := le_of_lt h
      have h2 : j + 1 ≤ P₁.n := h
      simp only [h1, h2, if_pos]
      exact P₁.mono j h
    · have h1 : j ≤ P₁.n := le_of_eq h
      have h2 : ¬ (j + 1 ≤ P₁.n) := by omega
      have heq : j + 1 - P₁.n = 1 := by omega
      simp only [h1, if_pos, h2, if_false, heq]
      have hpos : 0 < P₂.n := by omega
      have := P₂.mono 0 hpos
      rw [P₂.first] at this
      rw [h, P₁.last]
      simpa using this
    · have h1 : ¬ (j ≤ P₁.n) := by omega
      have h2 : ¬ (j + 1 ≤ P₁.n) := by omega
      simp only [h1, h2, if_false]
      have hlt : j - P₁.n < P₂.n := by omega
      have := P₂.mono (j - P₁.n) hlt
      have heq : j + 1 - P₁.n = (j - P₁.n) + 1 := by omega
      rw [heq]
      exact this

lemma psum_merge {a c b : ℝ} (g : ℝ → ℝ → ℝ) (P₁ : Partition a c) (P₂ : Partition c b) :
    psum g (merge P₁ P₂) = psum g P₁ + psum g P₂ := by
  unfold psum
  show ∑ i ∈ Finset.range (P₁.n + P₂.n),
      g ((merge P₁ P₂).x i) ((merge P₁ P₂).x (i + 1)) = _
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < P₁.n := Finset.mem_range.mp hi
    have h1 : i ≤ P₁.n := le_of_lt hi'
    have h2 : i + 1 ≤ P₁.n := hi'
    show g (if i ≤ P₁.n then P₁.x i else P₂.x (i - P₁.n))
        (if i + 1 ≤ P₁.n then P₁.x (i + 1) else P₂.x (i + 1 - P₁.n)) = _
    simp only [h1, h2, if_pos]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < P₂.n := Finset.mem_range.mp hi
    show g (if P₁.n + i ≤ P₁.n then P₁.x (P₁.n + i) else P₂.x (P₁.n + i - P₁.n))
        (if P₁.n + i + 1 ≤ P₁.n then P₁.x (P₁.n + i + 1) else P₂.x (P₁.n + i + 1 - P₁.n)) = _
    have h2 : ¬ (P₁.n + i + 1 ≤ P₁.n) := by omega
    have heq2 : P₁.n + i + 1 - P₁.n = i + 1 := by omega
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [Nat.add_zero, le_refl, if_pos, h2, if_false, heq2]
      rw [P₂.first, P₁.last]
    · have h1 : ¬ (P₁.n + i ≤ P₁.n) := by omega
      have heq1 : P₁.n + i - P₁.n = i := by omega
      simp only [h1, h2, if_false, heq1, heq2]

/-- The part of `P` to the left of a division point `c = P.x k`. -/
def splitLeft {a b : ℝ} (P : Partition a b) (k : ℕ) (hk : k ≤ P.n) (c : ℝ) (hc : P.x k = c) :
    Partition a c where
  n := k
  x := P.x
  first := P.first
  last := hc
  mono := fun i hi => P.mono i (lt_of_lt_of_le hi hk)

/-- The part of `P` to the right of a division point `c = P.x k`. -/
def splitRight {a b : ℝ} (P : Partition a b) (k : ℕ) (hk : k ≤ P.n) (c : ℝ) (hc : P.x k = c) :
    Partition c b where
  n := P.n - k
  x := fun j => P.x (k + j)
  first := by simpa using hc
  last := by
    show P.x (k + (P.n - k)) = b
    rw [Nat.add_sub_cancel' hk]
    exact P.last
  mono := by
    intro i hi
    have h : k + i < P.n := by omega
    exact P.mono (k + i) h

lemma psum_split {a b : ℝ} (g : ℝ → ℝ → ℝ) (P : Partition a b) (k : ℕ) (hk : k ≤ P.n) (c : ℝ)
    (hc : P.x k = c) :
    psum g P = psum g (splitLeft P k hk c hc) + psum g (splitRight P k hk c hc) := by
  unfold psum
  show ∑ i ∈ Finset.range P.n, g (P.x i) (P.x (i + 1))
      = (∑ i ∈ Finset.range k, g (P.x i) (P.x (i + 1)))
        + ∑ i ∈ Finset.range (P.n - k), g (P.x (k + i)) (P.x (k + (i + 1)))
  conv_lhs => rw [show P.n = k + (P.n - k) from (Nat.add_sub_cancel' hk).symm]
  rw [Finset.sum_range_add]
  congr 1

/-- Every partition has a refinement having `c` among its division points. -/
lemma exists_refinement_with_point {a b : ℝ} (P : Partition a b) (c : ℝ) (hc : c ∈ Set.Icc a b) :
    ∃ P' : Partition a b, Refines P' P ∧ ∃ k, ∃ _ : k ≤ P'.n, P'.x k = c := by
  classical
  have hex : ∃ j, c ≤ P.x j := ⟨P.n, by rw [P.last]; exact hc.2⟩
  set k := Nat.find hex with hkdef
  have hkspec : c ≤ P.x k := Nat.find_spec hex
  have hkmin : ∀ j, j < k → P.x j < c := fun j hj => lt_of_not_ge (Nat.find_min hex hj)
  have hkn : k ≤ P.n := Nat.find_min' hex (by rw [P.last]; exact hc.2)
  refine ⟨⟨P.n + 1, fun j => if j < k then P.x j else if j = k then c else P.x (j - 1), ?_, ?_, ?_⟩,
    ?_, k, ?_, ?_⟩
  · by_cases h : 0 < k
    · rw [if_pos h]
      exact P.first
    · have hk0 : k = 0 := by omega
      have hca : c ≤ a := by rw [← P.first, ← hk0]; exact hkspec
      rw [if_neg (by omega), if_pos (show 0 = k by omega)]
      exact le_antisymm hca hc.1
  · have h1 : ¬ (P.n + 1 < k) := by omega
    have h2 : ¬ (P.n + 1 = k) := by omega
    rw [if_neg h1, if_neg h2, Nat.add_sub_cancel]
    exact P.last
  · intro j hj
    rcases lt_trichotomy j k with h | h | h
    · rcases Nat.lt_or_ge (j + 1) k with h' | h'
      · have hjn : j < P.n := by omega
        rw [if_pos h, if_pos h']
        exact P.mono j hjn
      · have hjk : j + 1 = k := by omega
        have h2 : ¬ (j + 1 < k) := by omega
        rw [if_pos h, if_neg h2, if_pos hjk]
        exact le_of_lt (hkmin j h)
    · have h1 : ¬ (j < k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_pos h, if_neg h2, if_neg h3, show j + 1 - 1 = k by omega]
      exact hkspec
    · have h1 : ¬ (j < k) := by omega
      have h1' : ¬ (j = k) := by omega
      have h2 : ¬ (j + 1 < k) := by omega
      have h3 : ¬ (j + 1 = k) := by omega
      rw [if_neg h1, if_neg h1', if_neg h2, if_neg h3, show j + 1 - 1 = j by omega]
      have hjn : j - 1 < P.n := by omega
      have := P.mono (j - 1) hjn
      have heq2 : j - 1 + 1 = j := by omega
      rwa [heq2] at this
  · intro i hi
    by_cases h : i < k
    · refine ⟨i, ?_, ?_⟩
      · show i ≤ P.n + 1
        omega
      · show (if i < k then P.x i else if i = k then c else P.x (i - 1)) = P.x i
        rw [if_pos h]
    · refine ⟨i + 1, ?_, ?_⟩
      · show i + 1 ≤ P.n + 1
        omega
      · show (if i + 1 < k then P.x (i + 1) else if i + 1 = k then c else P.x (i + 1 - 1)) = P.x i
        rw [if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
  · show k ≤ P.n + 1
    omega
  · show (if k < k then P.x k else if k = k then c else P.x (k - 1)) = c
    rw [if_neg (by omega), if_pos rfl]

/-! ### Analytic part: bounds, and additivity of the upper and lower integrals -/

/-- The trivial partition `{a, b}`. -/
def trivialPartition {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  x := fun i => if i = 0 then a else b
  first := by norm_num
  last := by norm_num
  mono := by
    intro i hi
    have : i = 0 := by omega
    subst this
    norm_num
    exact hab

lemma abs_sSup_image_le {f : ℝ → ℝ} {u v M : ℝ} (huv : u ≤ v)
    (hM : ∀ y ∈ Set.Icc u v, |f y| ≤ M) : |sSup (f '' Set.Icc u v)| ≤ M := by
  have hmem : f u ∈ f '' Set.Icc u v := ⟨u, ⟨le_refl u, huv⟩, rfl⟩
  have hne : (f '' Set.Icc u v).Nonempty := ⟨f u, hmem⟩
  have hub : ∀ z ∈ f '' Set.Icc u v, z ≤ M := by
    rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y hy)).2
  have hbdd : BddAbove (f '' Set.Icc u v) := ⟨M, hub⟩
  refine abs_le.mpr ⟨?_, csSup_le hne hub⟩
  exact le_trans (abs_le.mp (hM u ⟨le_refl u, huv⟩)).1 (le_csSup hbdd hmem)

lemma abs_sInf_image_le {f : ℝ → ℝ} {u v M : ℝ} (huv : u ≤ v)
    (hM : ∀ y ∈ Set.Icc u v, |f y| ≤ M) : |sInf (f '' Set.Icc u v)| ≤ M := by
  have hmem : f u ∈ f '' Set.Icc u v := ⟨u, ⟨le_refl u, huv⟩, rfl⟩
  have hne : (f '' Set.Icc u v).Nonempty := ⟨f u, hmem⟩
  have hlb : ∀ z ∈ f '' Set.Icc u v, -M ≤ z := by
    rintro _ ⟨y, hy, rfl⟩; exact (abs_le.mp (hM y hy)).1
  have hbdd : BddBelow (f '' Set.Icc u v) := ⟨-M, hlb⟩
  refine abs_le.mpr ⟨le_csInf hne hlb, ?_⟩
  exact le_trans (csInf_le hbdd hmem) (abs_le.mp (hM u ⟨le_refl u, huv⟩)).2

/-- Telescoping of the increments of `α` along a partition. -/
lemma sum_delta {a b : ℝ} (α : ℝ → ℝ) (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, (α (P.x (i + 1)) - α (P.x i)) = α b - α a := by
  rw [Finset.sum_range_sub (fun i => α (P.x i)) P.n, P.first, P.last]

lemma delta_nonneg {u v : ℝ} {α : ℝ → ℝ} (hα : MonotoneOn α (Set.Icc u v)) (P : Partition u v)
    {i : ℕ} (hi : i < P.n) : 0 ≤ α (P.x (i + 1)) - α (P.x i) := by
  have h1 : P.x i ∈ Set.Icc u v := px_mem P (le_of_lt hi)
  have h2 : P.x (i + 1) ∈ Set.Icc u v := px_mem P hi
  have := hα h1 h2 (P.mono i hi)
  linarith

/-- An upper sum over a subinterval of `[a, b]` is bounded by `M (α b - α a)`. -/
lemma abs_upperSum_le {a b u v M : ℝ} {f α : ℝ → ℝ} (hM0 : 0 ≤ M)
    (hau : a ≤ u) (hvb : v ≤ b) (huv : u ≤ v)
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ y ∈ Set.Icc a b, |f y| ≤ M) (P : Partition u v) :
    |upperSum f α P| ≤ M * (α b - α a) := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  have hαuv : MonotoneOn α (Set.Icc u v) := hα.mono hsub
  have key : ∀ i ∈ Finset.range P.n,
      |sSup (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))|
        ≤ M * (α (P.x (i + 1)) - α (P.x i)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have hxi : P.x i ∈ Set.Icc u v := px_mem P (le_of_lt hi')
    have hxi1 : P.x (i + 1) ∈ Set.Icc u v := px_mem P hi'
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hbd : ∀ y ∈ Set.Icc (P.x i) (P.x (i + 1)), |f y| ≤ M := by
      intro y hy
      exact hM y (hsub ⟨le_trans hxi.1 hy.1, le_trans hy.2 hxi1.2⟩)
    have h1 := abs_sSup_image_le hle hbd
    have h2 : 0 ≤ α (P.x (i + 1)) - α (P.x i) := delta_nonneg hαuv P hi'
    rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_right h1 h2
  calc |upperSum f α P| ≤ ∑ i ∈ Finset.range P.n, M * (α (P.x (i + 1)) - α (P.x i)) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum key)
    _ = M * (α v - α u) := by rw [← Finset.mul_sum, sum_delta α P]
    _ ≤ M * (α b - α a) := by
        have h1 : α a ≤ α u := hα (Set.left_mem_Icc.mpr (le_trans hau (le_trans huv hvb)))
          (hsub (Set.left_mem_Icc.mpr huv)) hau
        have h2 : α v ≤ α b := hα (hsub (Set.right_mem_Icc.mpr huv))
          (Set.right_mem_Icc.mpr (le_trans hau (le_trans huv hvb))) hvb
        nlinarith
  
/-- A lower sum over a subinterval of `[a, b]` is bounded by `M (α b - α a)`. -/
lemma abs_lowerSum_le {a b u v M : ℝ} {f α : ℝ → ℝ} (hM0 : 0 ≤ M)
    (hau : a ≤ u) (hvb : v ≤ b) (huv : u ≤ v)
    (hα : MonotoneOn α (Set.Icc a b)) (hM : ∀ y ∈ Set.Icc a b, |f y| ≤ M) (P : Partition u v) :
    |lowerSum f α P| ≤ M * (α b - α a) := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  have hαuv : MonotoneOn α (Set.Icc u v) := hα.mono hsub
  have key : ∀ i ∈ Finset.range P.n,
      |sInf (f '' Set.Icc (P.x i) (P.x (i + 1))) * (α (P.x (i + 1)) - α (P.x i))|
        ≤ M * (α (P.x (i + 1)) - α (P.x i)) := by
    intro i hi
    have hi' : i < P.n := Finset.mem_range.mp hi
    have hxi : P.x i ∈ Set.Icc u v := px_mem P (le_of_lt hi')
    have hxi1 : P.x (i + 1) ∈ Set.Icc u v := px_mem P hi'
    have hle : P.x i ≤ P.x (i + 1) := P.mono i hi'
    have hbd : ∀ y ∈ Set.Icc (P.x i) (P.x (i + 1)), |f y| ≤ M := by
      intro y hy
      exact hM y (hsub ⟨le_trans hxi.1 hy.1, le_trans hy.2 hxi1.2⟩)
    have h1 := abs_sInf_image_le hle hbd
    have h2 : 0 ≤ α (P.x (i + 1)) - α (P.x i) := delta_nonneg hαuv P hi'
    rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_mul_of_nonneg_right h1 h2
  calc |lowerSum f α P| ≤ ∑ i ∈ Finset.range P.n, M * (α (P.x (i + 1)) - α (P.x i)) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum key)
    _ = M * (α v - α u) := by rw [← Finset.mul_sum, sum_delta α P]
    _ ≤ M * (α b - α a) := by
        have h1 : α a ≤ α u := hα (Set.left_mem_Icc.mpr (le_trans hau (le_trans huv hvb)))
          (hsub (Set.left_mem_Icc.mpr huv)) hau
        have h2 : α v ≤ α b := hα (hsub (Set.right_mem_Icc.mpr huv))
          (Set.right_mem_Icc.mpr (le_trans hau (le_trans huv hvb))) hvb
        nlinarith

/-- Splitting of an infimum over sums. -/
lemma csInf_eq_add {S T U : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty)
    (hSb : BddBelow S) (hTb : BddBelow T) (hUb : BddBelow U)
    (h1 : ∀ t ∈ T, ∀ u ∈ U, t + u ∈ S)
    (h2 : ∀ y ∈ S, ∃ t ∈ T, ∃ u ∈ U, t + u ≤ y) :
    sInf S = sInf T + sInf U := by
  refine le_antisymm (le_of_forall_pos_le_add ?_) (le_csInf hS ?_)
  · intro ε hε
    obtain ⟨t, htT, ht⟩ := exists_lt_of_csInf_lt hT (show sInf T < sInf T + ε / 2 by linarith)
    obtain ⟨u, huU, hu⟩ := exists_lt_of_csInf_lt hU (show sInf U < sInf U + ε / 2 by linarith)
    have : sInf S ≤ t + u := csInf_le hSb (h1 t htT u huU)
    linarith
  · intro y hy
    obtain ⟨t, htT, u, huU, hle⟩ := h2 y hy
    have h3 : sInf T ≤ t := csInf_le hTb htT
    have h4 : sInf U ≤ u := csInf_le hUb huU
    linarith

/-- Splitting of a supremum over sums. -/
lemma csSup_eq_add {S T U : Set ℝ} (hS : S.Nonempty) (hT : T.Nonempty) (hU : U.Nonempty)
    (hSb : BddAbove S) (hTb : BddAbove T) (hUb : BddAbove U)
    (h1 : ∀ t ∈ T, ∀ u ∈ U, t + u ∈ S)
    (h2 : ∀ y ∈ S, ∃ t ∈ T, ∃ u ∈ U, y ≤ t + u) :
    sSup S = sSup T + sSup U := by
  refine le_antisymm (csSup_le hS ?_) (le_of_forall_pos_le_add ?_)
  · intro y hy
    obtain ⟨t, htT, u, huU, hle⟩ := h2 y hy
    have h3 : t ≤ sSup T := le_csSup hTb htT
    have h4 : u ≤ sSup U := le_csSup hUb huU
    linarith
  · intro ε hε
    obtain ⟨t, htT, ht⟩ := exists_lt_of_lt_csSup hT (show sSup T - ε / 2 < sSup T by linarith)
    obtain ⟨u, huU, hu⟩ := exists_lt_of_lt_csSup hU (show sSup U - ε / 2 < sSup U by linarith)
    have : t + u ≤ sSup S := le_csSup hSb (h1 t htT u huU)
    linarith

lemma upperSum_merge {a c b : ℝ} (f α : ℝ → ℝ) (P₁ : Partition a c) (P₂ : Partition c b) :
    upperSum f α (merge P₁ P₂) = upperSum f α P₁ + upperSum f α P₂ :=
  psum_merge (fun u v => sSup (f '' Set.Icc u v) * (α v - α u)) P₁ P₂

lemma lowerSum_merge {a c b : ℝ} (f α : ℝ → ℝ) (P₁ : Partition a c) (P₂ : Partition c b) :
    lowerSum f α (merge P₁ P₂) = lowerSum f α P₁ + lowerSum f α P₂ :=
  psum_merge (fun u v => sInf (f '' Set.Icc u v) * (α v - α u)) P₁ P₂

lemma upperSum_split {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) (k : ℕ) (hk : k ≤ P.n) (c : ℝ)
    (hc : P.x k = c) :
    upperSum f α P
      = upperSum f α (splitLeft P k hk c hc) + upperSum f α (splitRight P k hk c hc) :=
  psum_split (fun u v => sSup (f '' Set.Icc u v) * (α v - α u)) P k hk c hc

lemma lowerSum_split {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) (k : ℕ) (hk : k ≤ P.n) (c : ℝ)
    (hc : P.x k = c) :
    lowerSum f α P
      = lowerSum f α (splitLeft P k hk c hc) + lowerSum f α (splitRight P k hk c hc) :=
  psum_split (fun u v => sInf (f '' Set.Icc u v) * (α v - α u)) P k hk c hc

/-- The upper integral is additive over adjacent intervals. -/
lemma upperIntegral_add {a c b M : ℝ} {f α : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hα : MonotoneOn α (Set.Icc a b)) (hM0 : 0 ≤ M) (hM : ∀ y ∈ Set.Icc a b, |f y| ≤ M) :
    upperIntegral a b f α = upperIntegral a c f α + upperIntegral c b f α := by
  have hab : a ≤ b := le_trans hac hcb
  refine csInf_eq_add ⟨upperSum f α (trivialPartition hab), ⟨_, rfl⟩⟩
    ⟨upperSum f α (trivialPartition hac), ⟨_, rfl⟩⟩
    ⟨upperSum f α (trivialPartition hcb), ⟨_, rfl⟩⟩ ?_ ?_ ?_ ?_ ?_
  · exact ⟨-(M * (α b - α a)), by
      rintro y ⟨P, rfl⟩
      have := abs_upperSum_le hM0 (le_refl a) (le_refl b) hab hα hM P
      linarith [(abs_le.mp this).1]⟩
  · exact ⟨-(M * (α b - α a)), by
      rintro y ⟨P, rfl⟩
      have := abs_upperSum_le hM0 (le_refl a) hcb hac hα hM P
      linarith [(abs_le.mp this).1]⟩
  · exact ⟨-(M * (α b - α a)), by
      rintro y ⟨P, rfl⟩
      have := abs_upperSum_le hM0 hac (le_refl b) hcb hα hM P
      linarith [(abs_le.mp this).1]⟩
  · rintro t ⟨P₁, rfl⟩ u ⟨P₂, rfl⟩
    exact ⟨merge P₁ P₂, (upperSum_merge f α P₁ P₂).symm⟩
  · rintro y ⟨P, rfl⟩
    obtain ⟨P', href, k, hk, hxk⟩ := exists_refinement_with_point P c ⟨hac, hcb⟩
    have hle : upperSum f α P' ≤ upperSum f α P :=
      (ch06_refinement a b hab f α hα ⟨M, hM⟩ P P' href).2
    refine ⟨upperSum f α (splitLeft P' k hk c hxk), ⟨_, rfl⟩,
      upperSum f α (splitRight P' k hk c hxk), ⟨_, rfl⟩, ?_⟩
    rw [← upperSum_split f α P' k hk c hxk]
    exact hle

/-- The lower integral is additive over adjacent intervals. -/
lemma lowerIntegral_add {a c b M : ℝ} {f α : ℝ → ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hα : MonotoneOn α (Set.Icc a b)) (hM0 : 0 ≤ M) (hM : ∀ y ∈ Set.Icc a b, |f y| ≤ M) :
    lowerIntegral a b f α = lowerIntegral a c f α + lowerIntegral c b f α := by
  have hab : a ≤ b := le_trans hac hcb
  refine csSup_eq_add ⟨lowerSum f α (trivialPartition hab), ⟨_, rfl⟩⟩
    ⟨lowerSum f α (trivialPartition hac), ⟨_, rfl⟩⟩
    ⟨lowerSum f α (trivialPartition hcb), ⟨_, rfl⟩⟩ ?_ ?_ ?_ ?_ ?_
  · exact ⟨M * (α b - α a), by
      rintro y ⟨P, rfl⟩
      exact (abs_le.mp (abs_lowerSum_le hM0 (le_refl a) (le_refl b) hab hα hM P)).2⟩
  · exact ⟨M * (α b - α a), by
      rintro y ⟨P, rfl⟩
      exact (abs_le.mp (abs_lowerSum_le hM0 (le_refl a) hcb hac hα hM P)).2⟩
  · exact ⟨M * (α b - α a), by
      rintro y ⟨P, rfl⟩
      exact (abs_le.mp (abs_lowerSum_le hM0 hac (le_refl b) hcb hα hM P)).2⟩
  · rintro t ⟨P₁, rfl⟩ u ⟨P₂, rfl⟩
    exact ⟨merge P₁ P₂, (lowerSum_merge f α P₁ P₂).symm⟩
  · rintro y ⟨P, rfl⟩
    obtain ⟨P', href, k, hk, hxk⟩ := exists_refinement_with_point P c ⟨hac, hcb⟩
    have hle : lowerSum f α P ≤ lowerSum f α P' :=
      (ch06_refinement a b hab f α hα ⟨M, hM⟩ P P' href).1
    refine ⟨lowerSum f α (splitLeft P' k hk c hxk), ⟨_, rfl⟩,
      lowerSum f α (splitRight P' k hk c hxk), ⟨_, rfl⟩, ?_⟩
    rw [← lowerSum_split f α P' k hk c hxk]
    exact hle

end RudinAdd

open Rudin RudinAdd in
/-- The upper integral and the lower integral are each additive over adjacent intervals, for a
bounded integrand and a monotonically increasing integrator; no integrability is assumed. -/
theorem solution (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    upperIntegral a b f α = upperIntegral a c f α + upperIntegral c b f α ∧
    lowerIntegral a b f α = lowerIntegral a c f α + lowerIntegral c b f α := by
  obtain ⟨M, hM⟩ := hfb
  have hab : a ≤ b := le_trans hac hcb
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (f a)) (hM a ⟨le_refl a, hab⟩)
  exact ⟨upperIntegral_add hac hcb hα hM0 hM, lowerIntegral_add hac hcb hα hM0 hM⟩

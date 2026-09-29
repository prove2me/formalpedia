-- Prove2me | solution 1 for Rudin.ch06_fundamental_theorem_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-18T20:50:26.926977+00:00
-- url     : https://prove2.me/submissions/13f2ed6b-a460-45f8-a2f4-1016ea62c217

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace RudinFTCSandwich

open Rudin

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

/-- Every division point of a partition of `[a, b]` lies in `[a, b]`. -/
lemma px_mem {a b : ℝ} (P : Partition a b) {i : ℕ} (hi : i ≤ P.n) : P.x i ∈ Set.Icc a b := by
  constructor
  · have := px_mono P (Nat.zero_le i) hi
    rwa [P.first] at this
  · have := px_mono P hi (le_refl P.n)
    rwa [P.last] at this

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
    simpa using hab

/-- The mean value theorem on a subinterval: the increment of `F` is `f t` times the length
for some `t` in the subinterval. -/
lemma exists_mvt {a b u v : ℝ} {f F : ℝ → ℝ} (hau : a ≤ u) (huv : u < v) (hvb : v ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    ∃ t ∈ Set.Icc u v, F v - F u = f t * (v - u) := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  have hcont : ContinuousOn F (Set.Icc u v) := fun x hx =>
    ((hF x (hsub hx)).continuousAt).continuousWithinAt
  obtain ⟨t, ht, hslope⟩ :=
    exists_hasDerivAt_eq_slope F f huv hcont
      (fun x hx => hF x (hsub (Set.Ioo_subset_Icc_self hx)))
  refine ⟨t, Set.Ioo_subset_Icc_self ht, ?_⟩
  have hne : v - u ≠ 0 := by linarith
  field_simp at hslope
  linarith [hslope]

/-- If `f` is bounded below on `[a, b]`, the infimum of `f` on a subinterval times the length of
that subinterval is at most the increment of `F`. -/
lemma increment_lower {a b u v m : ℝ} {f F : ℝ → ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hm : ∀ x ∈ Set.Icc a b, m ≤ f x) :
    sInf (f '' Set.Icc u v) * (v - u) ≤ F v - F u := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst heq; simp
  · obtain ⟨t, htmem, hFt⟩ := exists_mvt hau hlt hvb hF
    have hbdd : BddBelow (f '' Set.Icc u v) :=
      ⟨m, by rintro _ ⟨y, hy, rfl⟩; exact hm y (hsub hy)⟩
    have hmem : f t ∈ f '' Set.Icc u v := ⟨t, htmem, rfl⟩
    rw [hFt]
    exact mul_le_mul_of_nonneg_right (csInf_le hbdd hmem) (by linarith)

/-- If `f` is bounded above on `[a, b]`, the increment of `F` is at most the supremum of `f` on a
subinterval times the length of that subinterval. -/
lemma increment_upper {a b u v M : ℝ} {f F : ℝ → ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hM : ∀ x ∈ Set.Icc a b, f x ≤ M) :
    F v - F u ≤ sSup (f '' Set.Icc u v) * (v - u) := by
  have hsub : Set.Icc u v ⊆ Set.Icc a b := Set.Icc_subset_Icc hau hvb
  rcases eq_or_lt_of_le huv with heq | hlt
  · subst heq; simp
  · obtain ⟨t, htmem, hFt⟩ := exists_mvt hau hlt hvb hF
    have hbdd : BddAbove (f '' Set.Icc u v) :=
      ⟨M, by rintro _ ⟨y, hy, rfl⟩; exact hM y (hsub hy)⟩
    have hmem : f t ∈ f '' Set.Icc u v := ⟨t, htmem, rfl⟩
    rw [hFt]
    exact mul_le_mul_of_nonneg_right (le_csSup hbdd hmem) (by linarith)

/-- The telescoping identity for the increments of `F` along a partition. -/
lemma telescope {a b : ℝ} {F : ℝ → ℝ} (P : Partition a b) :
    ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) = F b - F a := by
  rw [Finset.sum_range_sub (fun i => F (P.x i)) P.n, P.first, P.last]

/-- If `f` is bounded below on `[a, b]`, every lower sum of `f` is at most `F b - F a`. -/
lemma lowerSum_le {a b m : ℝ} {f F : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hm : ∀ x ∈ Set.Icc a b, m ≤ f x) (P : Partition a b) :
    lowerSum f id P ≤ F b - F a := by
  calc lowerSum f id P
      ≤ ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' : i < P.n := Finset.mem_range.mp hi
        have h1 : P.x i ∈ Set.Icc a b := px_mem P (le_of_lt hi')
        have h2 : P.x (i + 1) ∈ Set.Icc a b := px_mem P hi'
        simpa using increment_lower h1.1 (P.mono i hi') h2.2 hF hm
    _ = F b - F a := telescope P

/-- If `f` is bounded above on `[a, b]`, `F b - F a` is at most every upper sum of `f`. -/
lemma le_upperSum {a b M : ℝ} {f F : ℝ → ℝ}
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hM : ∀ x ∈ Set.Icc a b, f x ≤ M) (P : Partition a b) :
    F b - F a ≤ upperSum f id P := by
  calc F b - F a = ∑ i ∈ Finset.range P.n, (F (P.x (i + 1)) - F (P.x i)) := (telescope P).symm
    _ ≤ upperSum f id P := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi' : i < P.n := Finset.mem_range.mp hi
        have h1 : P.x i ∈ Set.Icc a b := px_mem P (le_of_lt hi')
        have h2 : P.x (i + 1) ∈ Set.Icc a b := px_mem P hi'
        simpa using increment_upper h1.1 (P.mono i hi') h2.2 hF hM

end RudinFTCSandwich

open Rudin RudinFTCSandwich in
/-- Rudin, Theorem 6.21 in sandwich form, with one-sided boundedness and no integrability
hypothesis: if `F` is differentiable on `[a, b]` with `F' = f`, then `F b - F a` lies above the
lower integral of `f` as soon as `f` is bounded below, and below the upper integral of `f` as soon
as `f` is bounded above; consequently, for `f` bounded below and Riemann integrable,
`∫ₐᵇ f dx ≤ F b - F a`. -/
theorem solution (a b : ℝ) (hab : a ≤ b) (f F : ℝ → ℝ)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x) :
    ((∃ m, ∀ x ∈ Set.Icc a b, m ≤ f x) → lowerIntegral a b f id ≤ F b - F a) ∧
      ((∃ M, ∀ x ∈ Set.Icc a b, f x ≤ M) → F b - F a ≤ upperIntegral a b f id) ∧
      ((∃ m, ∀ x ∈ Set.Icc a b, m ≤ f x) → RiemannIntegrable a b f →
        RiemannIntegral a b f ≤ F b - F a) := by
  have hlow : (∃ m, ∀ x ∈ Set.Icc a b, m ≤ f x) → lowerIntegral a b f id ≤ F b - F a := by
    rintro ⟨m, hm⟩
    refine csSup_le ⟨lowerSum f id (trivialPartition hab), ⟨_, rfl⟩⟩ ?_
    rintro y ⟨P, rfl⟩
    exact lowerSum_le hF hm P
  have hupp : (∃ M, ∀ x ∈ Set.Icc a b, f x ≤ M) → F b - F a ≤ upperIntegral a b f id := by
    rintro ⟨M, hM⟩
    refine le_csInf ⟨upperSum f id (trivialPartition hab), ⟨_, rfl⟩⟩ ?_
    rintro y ⟨P, rfl⟩
    exact le_upperSum hF hM P
  refine ⟨hlow, hupp, ?_⟩
  intro hm hint
  have hEq : upperIntegral a b f id = lowerIntegral a b f id := hint
  have : RiemannIntegral a b f = upperIntegral a b f id := rfl
  rw [this, hEq]
  exact hlow hm

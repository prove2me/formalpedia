-- Prove2me | solution 1 for PebblingLean.FiniteProbability.uniformProbabilityReal_le_expect_div_of_event_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:02.038466+00:00
-- url     : https://prove2.me/submissions/ae84fc72-afa2-4970-8ecd-186d71f3cc5d

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}
namespace PebblingLean.FiniteProbability
theorem _root_.solution [Fintype Ω] [Nonempty Ω]
    {P : Ω → Prop} [DecidablePred P]
    (X : Ω → ℝ) {a : ℝ}
    (ha : 0 < a) (hnonneg : ∀ ω : Ω, 0 ≤ X ω)
    (hP : ∀ ω : Ω, P ω → a ≤ X ω) :
    uniformProbabilityReal P ≤ uniformExpectationReal X / a := by
  classical
  let bad : Finset Ω := Finset.univ.filter P
  have hsum_a_le : (∑ ω ∈ bad, a) ≤ ∑ ω ∈ bad, X ω := by
    exact Finset.sum_le_sum fun ω hω =>
      hP ω (by simpa [bad] using (Finset.mem_filter.mp hω).2)
  have hsum_bad_le_univ : (∑ ω ∈ bad, X ω) ≤ ∑ ω : Ω, X ω := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp [bad])
      (fun ω _hω _hnot => hnonneg ω)
  have hcard_mul_a_le_sum : (bad.card : ℝ) * a ≤ ∑ ω : Ω, X ω := by
    have hsum_const : (∑ _ω ∈ bad, a) = (bad.card : ℝ) * a := by
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← hsum_const]
    exact hsum_a_le.trans hsum_bad_le_univ
  have hcard_pos : 0 < (Fintype.card Ω : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hden_pos : 0 < (Fintype.card Ω : ℝ) * a := mul_pos hcard_pos ha
  have hrewrite : (bad.card : ℝ) / (Fintype.card Ω : ℝ) =
      ((bad.card : ℝ) * a) / ((Fintype.card Ω : ℝ) * a) := by
    field_simp [ha.ne', hcard_pos.ne']
  unfold uniformProbabilityReal uniformExpectationReal
  change (bad.card : ℝ) / (Fintype.card Ω : ℝ) ≤
    (∑ ω : Ω, X ω) / (Fintype.card Ω : ℝ) / a
  rw [hrewrite, div_div]
  exact div_le_div_of_nonneg_right hcard_mul_a_le_sum hden_pos.le
end PebblingLean.FiniteProbability

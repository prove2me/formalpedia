-- Prove2me | solution 1 for ProbabilityTheory.IndepFun.cond_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:33.471526+00:00
-- url     : https://prove2.me/submissions/b27927c7-5f86-4ca8-b397-db7fe88db4ae

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
variable {Ω α β : Type*} {_ : MeasurableSpace Ω} {_ : MeasurableSpace α} {_ :
  MeasurableSpace β}
  {μ : Measure Ω} {A : Ω → α} {B : Ω → β}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IndepFun
theorem _root_.solution (hi : IndepFun A B μ) {s : Set α}
    (hs : MeasurableSet s) (hA : Measurable A) :
    IndepFun A B (μ[| A⁻¹' s]) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2 (fun u v hu hv ↦ ?_)
  have : A ⁻¹' s ∩ (A ⁻¹' u ∩ B ⁻¹' v) = A ⁻¹' (s ∩ u) ∩ B ⁻¹' v := by aesop
  simp only [cond_apply (hA hs), this]
  rcases eq_or_ne (μ (A ⁻¹' s)) ∞ with h|h
  · simp [h]
  rcases eq_or_ne (μ (A ⁻¹' s)) 0 with h'|h'
  · have I : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' v) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_left.trans (preimage_mono inter_subset_left)
    have J : μ (A ⁻¹' s ∩ B ⁻¹' v) = 0 :=
      le_antisymm ((measure_mono inter_subset_left).trans h'.le) bot_le
    simp only [I, J, mul_zero]
  · rw [hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) hv, Set.preimage_inter,
      hi.measure_inter_preimage_eq_mul _ _ hs hv, ← mul_assoc (μ (A ⁻¹' s))⁻¹,
      ← mul_assoc (μ (A ⁻¹' s))⁻¹, ENNReal.inv_mul_cancel h' h, one_mul]
end _root_.ProbabilityTheory.IndepFun
end ProbabilityTheory

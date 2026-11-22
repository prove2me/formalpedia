-- Prove2me | solution 1 for ProbabilityTheory.IndepFun.cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:56.157807+00:00
-- url     : https://prove2.me/submissions/7cc52cbd-408d-48db-a967-af126d9bd428

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
theorem _root_.solution (hi : IndepFun A B μ) {s : Set α} {t : Set β}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hA : Measurable A) (hB : Measurable B) :
    IndepFun A B (μ[| A ⁻¹' s ∩ B ⁻¹' t]) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.2 (fun u v hu hv ↦ ?_)
  have I1 : A ⁻¹' s ∩ B ⁻¹' t ∩ (A ⁻¹' u ∩ B ⁻¹' v) =
    A ⁻¹' (s ∩ u) ∩ B ⁻¹' (t ∩ v) := by aesop
  have I2 : A ⁻¹' s ∩ B ⁻¹' t ∩ A ⁻¹' u = A ⁻¹' (s ∩ u) ∩ B ⁻¹' t := by aesop
  have I3 : A ⁻¹' s ∩ B ⁻¹' t ∩ B ⁻¹' v = A ⁻¹' s ∩ B ⁻¹' (t ∩ v) := by aesop
  simp only [cond_apply ((hA hs).inter (hB ht)), I1, I2, I3]
  rcases eq_or_ne (μ (A ⁻¹' s ∩ B⁻¹' t)) ∞ with h|h
  · simp [h]
  rcases eq_or_ne (μ (A ⁻¹' s ∩ B⁻¹' t)) 0 with h'|h'
  · have I : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' (t ∩ v)) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_inter (preimage_mono inter_subset_left)
        (preimage_mono inter_subset_left)
    have J : μ (A ⁻¹' (s ∩ u) ∩ B ⁻¹' t) = 0 := by
      apply le_antisymm ((measure_mono _).trans h'.le) bot_le
      exact inter_subset_inter_left _ (preimage_mono inter_subset_left)
    simp only [I, J, mul_zero, zero_mul]
  · simp only [hi.measure_inter_preimage_eq_mul _ _ hs ht, ne_eq, mul_eq_zero, not_or] at h'
    simp only [hi.measure_inter_preimage_eq_mul _ _ hs ht, ne_eq, ENNReal.mul_eq_top, h'.1,
      not_false_eq_true, true_and, h'.2, and_true, not_or] at h
    rw [mul_assoc]
    congr 1
    rw [hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) (ht.inter hv),
      hi.measure_inter_preimage_eq_mul _ _ (hs.inter hu) ht,
      hi.measure_inter_preimage_eq_mul _ _ hs ht,
      hi.measure_inter_preimage_eq_mul _ _ hs (ht.inter hv),
      ENNReal.mul_inv (Or.inl h'.1) (Or.inr h'.2), mul_assoc]
    congr 1
    have : μ (B ⁻¹' t) *
          ((μ (A ⁻¹' s))⁻¹ * (μ (B ⁻¹' t))⁻¹ *
            (μ (A ⁻¹' s) * μ (B ⁻¹' (t ∩ v))))
      = (μ (B ⁻¹' t) * (μ (B ⁻¹' t))⁻¹) *
        ((μ (A ⁻¹' s))⁻¹ * μ (A ⁻¹' s)) * μ (B ⁻¹' (t ∩ v)) := by
        ring
    rw [this, ENNReal.inv_mul_cancel h'.1 h.2, ENNReal.mul_inv_cancel h'.2 h.1, one_mul, one_mul]
end _root_.ProbabilityTheory.IndepFun
end ProbabilityTheory

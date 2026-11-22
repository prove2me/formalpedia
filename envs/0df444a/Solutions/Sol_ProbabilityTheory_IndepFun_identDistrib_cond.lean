-- Prove2me | solution 1 for ProbabilityTheory.IndepFun.identDistrib_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:30.527846+00:00
-- url     : https://prove2.me/submissions/0f4729f5-b761-4f66-bd70-d47570551cbc

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence

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
theorem _root_.solution [IsProbabilityMeasure μ]
    (hi : IndepFun A B μ) {s : Set β}
    (hs : MeasurableSet s) (hA : Measurable A) (hB : Measurable B)
    (h : μ (B ⁻¹' s) ≠ 0) :
    IdentDistrib A A μ (μ[|B ⁻¹' s]) := by
  refine ⟨hA.aemeasurable, hA.aemeasurable, ?_⟩
  ext t ht
  rw [Measure.map_apply hA ht, Measure.map_apply hA ht, cond_apply (hB hs), Set.inter_comm,
    hi.measure_inter_preimage_eq_mul _ _ ht hs, mul_comm, mul_assoc,
    ENNReal.mul_inv_cancel h (by finiteness), mul_one]
end _root_.ProbabilityTheory.IndepFun
end ProbabilityTheory

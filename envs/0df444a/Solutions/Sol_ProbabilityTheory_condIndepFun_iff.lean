-- Prove2me | solution 1 for ProbabilityTheory.condIndepFun_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:56.055425+00:00
-- url     : https://prove2.me/submissions/a160c50f-5a57-4ec8-a047-3128dfa05269

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
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω
    → β} {h : Ω → γ}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution : CondIndepFun f g h μ ↔ ∀ᵐ z ∂ (μ.map h),
  IndepFun f g (μ[|h ← z]) := by rfl
end _root_.ProbabilityTheory
end ProbabilityTheory

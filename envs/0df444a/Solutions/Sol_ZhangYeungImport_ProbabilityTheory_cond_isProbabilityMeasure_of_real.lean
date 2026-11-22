-- Prove2me | solution 1 for ZhangYeungImport.ProbabilityTheory.cond_isProbabilityMeasure_of_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:43.1068+00:00
-- url     : https://prove2.me/submissions/feea28d8-9824-4411-9f6d-1da64deb1f86

module
public import Mathlib.Probability.ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
variable {Ω Ω' α : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'} {μ : Measure Ω}
  {s t : Set Ω}
open ProbabilityTheory
namespace ProbabilityTheory
theorem _root_.solution {α : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    {s : Set α} (hcs : μ.real s ≠ 0) :
    IsProbabilityMeasure μ[|s] := by
  apply cond_isProbabilityMeasure_of_finite
  · intro h
    simp [measureReal_def, h] at hcs
  · intro h
    simp [measureReal_def, h] at hcs
end ProbabilityTheory

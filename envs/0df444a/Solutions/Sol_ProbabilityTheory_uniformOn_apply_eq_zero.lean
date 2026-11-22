-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:37.348807+00:00
-- url     : https://prove2.me/submissions/f73bc698-1ac2-4f77-a070-64ba3e00c195

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution (hst : s ∩ t = ∅) : uniformOn s t = 0 := by
  rcases Set.finite_or_infinite s with hs | hs
  · exact (uniformOn_eq_zero_iff hs).mpr hst
  · simp [uniformOn, cond, Measure.count_apply_infinite hs]
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_apply_singleton_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:33.708952+00:00
-- url     : https://prove2.me/submissions/d8ecc2fc-09ff-4b0f-b6e8-910289da9b57

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
theorem _root_.solution (hx : x ∉ s) : uniformOn s {x} = 0 := by
  simp [uniformOn, cond, hx]
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.real_uniformOn_apply_singleton_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:01.206427+00:00
-- url     : https://prove2.me/submissions/216f1dec-7f2f-493f-ba14-cb91d5cc4417

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Theorems.Thm_ProbabilityTheory_uniformOn_apply_singleton_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution (hx : x ∉ s) :
    (uniformOn s).real {x} = 0 := by
  simp [measureReal_def, uniformOn_apply_singleton_of_not_mem hx]
end ProbabilityTheory

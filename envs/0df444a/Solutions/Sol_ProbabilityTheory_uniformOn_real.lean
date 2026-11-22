-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:26:56.877007+00:00
-- url     : https://prove2.me/submissions/5de61331-ac92-40c8-8a27-27420359b29a

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Theorems.Thm_ProbabilityTheory_uniformOn_apply

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution (hs : s.Finite) (t : Set Ω) :
    (uniformOn s).real t = (Nat.card ↑(s ∩ t)) / Nat.card s := by
  simp [measureReal_def, uniformOn_apply hs]
end ProbabilityTheory

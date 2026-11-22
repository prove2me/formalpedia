-- Prove2me | solution 1 for ProbabilityTheory.uniformOn_real_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:46:08.245143+00:00
-- url     : https://prove2.me/submissions/3d72d246-e334-4d54-9449-14b4dbb8f2aa

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Theorems.Thm_ProbabilityTheory_uniformOn_real
public import Theorems.Thm_Set_ncard_inter_singleton


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution (hs : s.Finite) (ω : Ω) [Decidable (ω ∈ s)] :
    (uniformOn s).real {ω} = if ω ∈ s then (s.ncard : ℝ)⁻¹ else 0 := by
  simp [uniformOn_real hs, Set.ncard_inter_singleton]; split <;> simp
end ProbabilityTheory

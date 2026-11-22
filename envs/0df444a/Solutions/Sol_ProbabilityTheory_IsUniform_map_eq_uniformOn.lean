-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.map_eq_uniformOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:38.538608+00:00
-- url     : https://prove2.me/submissions/635e51ea-deb3-4150-8b95-ca3969ae5e43

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_isUniform_uniformOn
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_of_isUniform

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Set
open scoped ENNReal
open ProbabilityTheory
universe uΩ uS uT uU
variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} [mΩ : MeasurableSpace Ω]
  {X : Ω → S} {Y : Ω → T} {μ : Measure Ω} {H : Set S}
variable [MeasurableSpace S] [DiscreteMeasurableSpace S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IsUniform
theorem _root_.solution [Countable S] [IsProbabilityMeasure μ]
    {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (hH : H.Finite) (h'H : H.Nonempty) :
    μ.map X = uniformOn H := by
  have : Finite H := hH
  have : IsProbabilityMeasure (uniformOn H) := isProbabilityMeasure_uniformOn hH h'H
  have : IdentDistrib X id μ (uniformOn (H : Set S)) :=
    .of_isUniform (H := H) hX measurable_id h isUniform_uniformOn
  simpa using this.map_eq
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.measureReal_preimage_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:14.708183+00:00
-- url     : https://prove2.me/submissions/83452a32-5fcb-4b11-bd20-1900c13e887a

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_of_mem

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
theorem _root_.solution
    {A : Finset S} [IsProbabilityMeasure μ]
    (h : IsUniform A X μ) (hX : Measurable X) {s : S} (hs : s ∈ A) :
    μ.real (X ⁻¹' {s}) = 1 / A.card := by
  simp [measureReal_def, h.measure_preimage_of_mem hX hs]
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory

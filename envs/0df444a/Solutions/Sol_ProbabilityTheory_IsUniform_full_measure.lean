-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.full_measure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:34.440495+00:00
-- url     : https://prove2.me/submissions/da453643-8a70-4108-a01c-9a8606697a09

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform

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
theorem _root_.solution (h : IsUniform H X μ) (hX : Measurable X) :
    (μ.map X) H = μ Set.univ := by
    rw [Measure.map_apply hX (by measurability)]
    refine measure_eq_measure_of_null_sdiff (subset_univ _) ?h_nulldiff
    convert h.measure_preimage_compl
    ext ω; simp
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory

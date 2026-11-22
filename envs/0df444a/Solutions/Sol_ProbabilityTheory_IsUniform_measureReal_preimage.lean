-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.measureReal_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:47:13.458219+00:00
-- url     : https://prove2.me/submissions/8c8da2e8-fefd-4f4b-9eac-79c41abba140

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage

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
    {H : Finset S} (h : IsUniform H X μ) (hX : Measurable X)
    (H' : Set S) :
    μ.real (X ⁻¹' H') = (μ.real univ) * (Nat.card (H' ∩ H).Elem) / Nat.card H := by
  simp [measureReal_def, h.measure_preimage hX H', ENNReal.toReal_div]
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory

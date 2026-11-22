-- Prove2me | solution 1 for ProbabilityTheory.IdentDistrib.of_isUniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:51.428831+00:00
-- url     : https://prove2.me/submissions/180fbe08-56a8-4606-b6d1-d223cfd210f7

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Theorems.Thm_ProbabilityTheory_IsUniform_measure_preimage_of_nmem
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
namespace _root_.ProbabilityTheory.IdentDistrib
theorem _root_.solution
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] [Finite H] [Countable S]
    {X : Ω → S} {X' : Ω' → S}
    (hX : Measurable X) (hX' : Measurable X') (hX_unif : IsUniform H X μ)
    (hX'_unif : IsUniform H X' μ') : IdentDistrib X X' μ μ' := by
  refine ⟨hX.aemeasurable, hX'.aemeasurable, ?_⟩
  ext E hE
  rw [← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE,
    ← MeasureTheory.Measure.tsum_indicator_apply_singleton _ _ hE]
  congr! 4 with _ x
  rw [Measure.map_apply hX (.singleton x), Measure.map_apply hX' (.singleton x)]
  set Hf := H.toFinite.toFinset
  have hX_unif' : IsUniform Hf X μ := by convert hX_unif; simp [Hf]
  have hX'_unif' : IsUniform Hf X' μ' := by convert hX'_unif; simp [Hf]
  by_cases h : x ∈ Hf
  · rw [IsUniform.measure_preimage_of_mem hX_unif' hX h,
      IsUniform.measure_preimage_of_mem hX'_unif' hX' h]
    simp
  · rw [IsUniform.measure_preimage_of_nmem hX_unif' h,
      IsUniform.measure_preimage_of_nmem hX'_unif' h]
end _root_.ProbabilityTheory.IdentDistrib
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.IsUniform.restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:42:40.108783+00:00
-- url     : https://prove2.me/submissions/776d0b40-3419-42e5-a46d-9bedaacd7a0d

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
theorem _root_.solution
    {H : Set S} (h : IsUniform H X μ) (hX : Measurable X) (H' : Set S) :
    IsUniform (H' ∩ H) X (μ[|X ⁻¹' H']) where
  eq_of_mem := fun x hx y hy ↦ by
    simp only [cond, Measure.smul_apply, smul_eq_mul]
    rw [μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hx.1)),
      μ.restrict_eq_self (preimage_mono (singleton_subset_iff.mpr hy.1)), h.eq_of_mem hx.2 hy.2]
  measure_preimage_compl := by
    rewrite [← nonpos_iff_eq_zero, Set.compl_inter, Set.preimage_union]
    calc
      _ ≤ (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + (μ[|X ⁻¹' H']) (X ⁻¹' Hᶜ) :=
        measure_union_le _ _
      _ = (μ[|X ⁻¹' H']) (X ⁻¹' H'ᶜ) + 0 := congrArg _ <| by
        simp only [cond, Measure.smul_apply, smul_eq_mul]
        convert mul_zero _
        exact eq_bot_mono (Measure.restrict_apply_le _ _) h.measure_preimage_compl
      _ = 0 := by
        simp only [cond, Measure.smul_apply, smul_eq_mul]
        rw [add_zero, Set.preimage_compl, Measure.restrict_apply <|
          MeasurableSet.compl (measurableSet_preimage hX .of_discrete),
          compl_inter_self, measure_empty, mul_zero]
end _root_.ProbabilityTheory.IsUniform
end ProbabilityTheory

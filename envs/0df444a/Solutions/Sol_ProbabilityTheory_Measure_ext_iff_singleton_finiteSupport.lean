-- Prove2me | solution 1 for ProbabilityTheory.Measure.ext_iff_singleton_finiteSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:56.840875+00:00
-- url     : https://prove2.me/submissions/efdc8408-1517-4003-939e-a1ebad842e41

module
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Dirac
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Real
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Measure
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal NNReal Topology
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] --[MeasurableSingletonClass S]
  [MeasurableSpace T] --[MeasurableSingletonClass T]
  [MeasurableSpace U]
variable {μ : Measure S}
variable [MeasurableSingletonClass S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.Measure
theorem _root_.solution
    {μ1 μ2 : Measure S} [FiniteSupport μ1] [FiniteSupport μ2] :
    μ1 = μ2 ↔ ∀ x, μ1 {x} = μ2 {x} := by
  classical
  constructor
  · simp_all
  · let A1 := μ1.finiteSupport
    have hA1 := measure_compl_support μ1
    let A2 := μ2.finiteSupport
    have hA2 := measure_compl_support μ2
    intro h
    ext s
    have h1 : μ1 s = μ1 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      refine measure_mono_null ?_ hA1
      intro x
      simp (config := { contextual := true }) [A1]
    have h2 : μ2 s = μ2 (s ∩ (A1 ∪ A2)) := by
      apply (measure_eq_measure_of_null_sdiff _ _).symm
      · simp
      exact measure_mono_null (fun x ↦ by simp (config := { contextual := true }) [A2]) hA2
    rw [h1, h2]
    have hs : Set.Finite (s ∩ (A1 ∪ A2)) := Set.toFinite (s ∩ (↑A1 ∪ ↑A2))
    rw [← hs.coe_toFinset, ← sum_measure_singleton (μ := μ1),
      ← sum_measure_singleton (μ := μ2)]
    simp_rw [h]
end _root_.ProbabilityTheory.Measure
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.integral_congr_finiteSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:53.321357+00:00
-- url     : https://prove2.me/submissions/1def07ac-2f8e-47bf-b476-840859523e73

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
theorem _root_.solution {μ : Measure Ω} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : Ω → G} [FiniteSupport μ]
    (hfg : ∀ x, μ {x} ≠ 0 → f x = g x) : ∫ x, f x ∂μ = ∫ x, g x ∂μ := by
  refine integral_congr_ae <| measure_mono_null ?_ <| measure_compl_support μ
  exact fun x hx hx' ↦ hx <| hfg _ <| mem_support.1 hx'
end ProbabilityTheory

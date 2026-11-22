-- Prove2me | solution 1 for ProbabilityTheory.mutualInfo_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:13.748807+00:00
-- url     : https://prove2.me/submissions/48e6a223-97b2-4af0-9e65-529406105d2b

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_indepFun_const


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution (hX : Measurable X) (c : T)
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    I[X : fun _ ↦ c; μ] = 0 :=
  (indepFun_const c).mutualInfo_eq_zero hX measurable_const
end _root_.ProbabilityTheory
end ProbabilityTheory

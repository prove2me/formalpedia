-- Prove2me | solution 1 for ProbabilityTheory.condMutualInfo_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:00:06.852912+00:00
-- url     : https://prove2.me/submissions/e857042a-5fb4-40b2-8ec9-36480bf41118

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condMutualInfo_eq_integral_mutualInfo
public import Theorems.Thm_ProbabilityTheory_ae_mem_of_finiteRange


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [MeasurableSingletonClass U] [IsFiniteMeasure μ]
    (hZ : Measurable Z) [FiniteRange Z] :
    I[X : Y | Z; μ] = ∑ z ∈ FiniteRange.toFinset Z,
      μ.real (Z ⁻¹' {z}) * I[X : Y; μ[|Z ← z]] := by
  rw [condMutualInfo_eq_integral_mutualInfo,
    integral_eq_setIntegral (ae_mem_of_finiteRange hZ),
    setIntegral_finset _ .finset]
  congr 1 with z
  rw [map_measureReal_apply hZ (MeasurableSet.singleton z)]
  rfl
end _root_.ProbabilityTheory
end ProbabilityTheory

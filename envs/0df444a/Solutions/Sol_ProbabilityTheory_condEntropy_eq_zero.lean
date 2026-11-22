-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:12:38.190963+00:00
-- url     : https://prove2.me/submissions/9104a415-cb7c-40f8-b667-556eea7ed0fd

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure



set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable {X : Ω → S} {Y : Ω → T}
variable [MeasurableSingletonClass T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    (hY : Measurable Y) (μ : Measure Ω) [IsFiniteMeasure μ] (t : T)
    (ht : (μ.map Y).real {t} = 0) : H[X | Y ← t; μ] = 0 := by
  convert entropy_zero_measure X
  apply cond_eq_zero_of_meas_eq_zero
  rw [map_measureReal_apply hY (.singleton t)] at ht
  rw [← measureReal_eq_zero_iff]
  exact ht
end _root_.ProbabilityTheory
end ProbabilityTheory

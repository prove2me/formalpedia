-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_eq_sum_sum_fintype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:12:56.517798+00:00
-- url     : https://prove2.me/submissions/e26f44c8-8ad2-4638-bee1-338bec4f0850

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_entropy_cond_eq_sum
public import Theorems.Thm_ProbabilityTheory_condEntropy_eq_sum_fintype

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
variable [MeasurableSingletonClass S]
omit [MeasurableSingletonClass S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution {Y : Ω → T} (hY : Measurable Y)
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype S] [Fintype T] :
    H[X | Y; μ] = ∑ y, ∑ x,
      (μ.map Y).real {y} * negMulLog (((μ[|Y ← y]).map X).real {x}) := by
  rw [condEntropy_eq_sum_fintype _ _ _ hY]
  congr with y
  rw [entropy_cond_eq_sum, tsum_fintype, Finset.mul_sum, map_measureReal_apply hY (.singleton _)]
end _root_.ProbabilityTheory
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:57:24.452996+00:00
-- url     : https://prove2.me/submissions/6e57f752-e082-4352-b810-5dcdeb88856b

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
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
variable {X : Ω → S} {Y : Ω → T}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω
  → T) (μ : Measure Ω)
    [IsFiniteMeasure μ] (hY : Measurable Y) [FiniteRange Y] :
    H[X | Y; μ] = ∑ y ∈ FiniteRange.toFinset Y,
      ((μ.map Y).real {y}) * H[X | Y ← y; μ] := by
  rw [condEntropy_def, integral_eq_setIntegral (ae_mem_of_finiteRange hY),
    setIntegral_finset _ .finset]
  simp_rw [smul_eq_mul]
end _root_.ProbabilityTheory
end ProbabilityTheory

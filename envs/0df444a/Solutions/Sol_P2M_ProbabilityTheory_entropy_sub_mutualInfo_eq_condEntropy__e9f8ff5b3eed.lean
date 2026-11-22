-- Prove2me | solution 1 for P2M_ProbabilityTheory_entropy_sub_mutualInfo_eq_condEntropy__e9f8ff5b3eed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:14:28.521804+00:00
-- url     : https://prove2.me/submissions/6f61c48e-527d-447c-a203-6f21c0a0f31a

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_P2M_ProbabilityTheory_mutualInfo_eq_entropy_sub_condEntropy__219a0bee1bfe

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
variable [Countable S] [Countable T]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    (hX : Measurable X) (hY : Measurable Y) (μ :
  Measure Ω)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    H[Y; μ] - I[X : Y; μ] = H[Y | X; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' hX hY, sub_sub_self]
end _root_.ProbabilityTheory
end ProbabilityTheory

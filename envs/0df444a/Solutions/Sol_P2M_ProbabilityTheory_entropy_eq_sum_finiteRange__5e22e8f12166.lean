-- Prove2me | solution 1 for P2M_ProbabilityTheory_entropy_eq_sum_finiteRange__5e22e8f12166
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:11:19.563811+00:00
-- url     : https://prove2.me/submissions/5a1be08b-75d6-4457-b9ae-31c726e82de9

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_entropy_eq_sum_finiteRange

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
namespace ProbabilityTheory
theorem _root_.solution [MeasurableSingletonClass S] (hX : Measurable X) {μ : Measure Ω}
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] :
    entropy X μ = ∑ x ∈ FiniteRange.toFinset X, negMulLog ((μ.map X).real {x}) :=
  entropy_eq_sum_finiteRange hX
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.entropy_pair_le_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:13:59.966339+00:00
-- url     : https://prove2.me/submissions/53fe22e2-9f99-4b66-b10a-70f6b2eb31b6

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_mutualInfo_nonneg
public import Theorems.Thm_ProbabilityTheory_Kernel_mutualInfo_nonneg


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
theorem _root_.solution
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) [FiniteRange X]
    [FiniteRange Y] : H[⟨X, Y⟩; μ] ≤ H[X; μ] + H[Y; μ] :=
  sub_nonneg.1 <| mutualInfo_nonneg hX hY _
end _root_.ProbabilityTheory
end ProbabilityTheory

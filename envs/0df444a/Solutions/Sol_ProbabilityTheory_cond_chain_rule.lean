-- Prove2me | solution 1 for ProbabilityTheory.cond_chain_rule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:06:57.61494+00:00
-- url     : https://prove2.me/submissions/05c7d926-f273-4127-8ce6-d143c8b1ec95

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condEntropy_comm
public import Theorems.Thm_P2M_ProbabilityTheory_cond_chain_rule__11c12758197b

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
variable [MeasurableSpace T]
variable [Countable S] [MeasurableSingletonClass S]
  [Countable T] [MeasurableSingletonClass T]
variable [Countable U] [MeasurableSingletonClass U]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) [FiniteRange X] [FiniteRange Y]
    [FiniteRange Z] :
    H[⟨X, Y⟩ | Z; μ] = H[Y | Z; μ] + H[X | ⟨Y, Z⟩; μ] := by
  rw [condEntropy_comm hX hY, cond_chain_rule' _ hY hX hZ]
end _root_.ProbabilityTheory
end ProbabilityTheory

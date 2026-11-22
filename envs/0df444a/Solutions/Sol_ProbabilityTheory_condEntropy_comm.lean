-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:58:59.666269+00:00
-- url     : https://prove2.me/submissions/be509484-55e3-43df-bd3a-13d5f3970dcb

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_condEntropy_comp_of_injective
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk


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
variable [Countable S]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution [Countable T] {Z : Ω → U}
    (hX : Measurable X) (hY : Measurable Y) (μ : Measure Ω) :
    H[⟨X, Y⟩ | Z; μ] = H[⟨Y, X⟩ | Z; μ] := by
  change H[⟨X, Y⟩ | Z; μ] = H[Prod.swap ∘ ⟨X, Y⟩ | Z; μ]
  exact (condEntropy_comp_of_injective μ (hX.prodMk hY) Prod.swap Prod.swap_injective).symm
end _root_.ProbabilityTheory
end ProbabilityTheory

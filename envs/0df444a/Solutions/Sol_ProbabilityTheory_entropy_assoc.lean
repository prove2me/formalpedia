-- Prove2me | solution 1 for ProbabilityTheory.entropy_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:57:13.120594+00:00
-- url     : https://prove2.me/submissions/fe8ed0ae-f8ab-4c51-9c55-bab404e0ec3f

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
open Set
open Function
variable [Countable S] [MeasurableSingletonClass S]
  [MeasurableSpace T] [MeasurableSingletonClass T]
  [Countable U] [MeasurableSingletonClass U]
variable [Countable T]
namespace ProbabilityTheory
theorem _root_.solution (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (μ : Measure Ω) :
    H[⟨X, ⟨Y, Z⟩⟩; μ] = H[⟨⟨X, Y⟩, Z⟩; μ] := by
  change H[MeasurableEquiv.prodAssoc ∘ ⟨⟨X, Y⟩, Z⟩; μ] = H[⟨⟨X, Y⟩, Z⟩; μ]
  exact entropy_comp_of_injective μ ((hX.prodMk hY).prodMk hZ) _ <| Equiv.injective _
end ProbabilityTheory

-- Prove2me | solution 1 for ProbabilityTheory.condEntropy_comp_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:07:36.075245+00:00
-- url     : https://prove2.me/submissions/bd847152-62d4-4de6-8659-c20ea44a8534

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_P2M_ProbabilityTheory_chain_rule___ff6bade4a15d
public import Theorems.Thm_ProbabilityTheory_entropy_submodular
public import Theorems.Thm_ProbabilityTheory_iIndepFun_prod


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
variable [Countable U] [MeasurableSingletonClass U]
variable (μ)
variable [Countable S] [Countable T]
variable [IsZeroOrProbabilityMeasure μ]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    [FiniteRange X] [FiniteRange Y] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (f : S
      → U) : H[Y | f ∘ X; μ] ≥ H[Y | X; μ] := by
  have h_joint : H[⟨Y, ⟨X, f ∘ X⟩⟩; μ] = H[⟨Y, X⟩; μ] := by
    let g : T × S → T × S × U := fun (y, x) ↦ (y, (x, f x))
    change H[g ∘ ⟨Y, X⟩; μ] = H[⟨Y, X⟩; μ]
    refine entropy_comp_of_injective μ (by exact Measurable.prod hY hX) g (fun _ _ h => ?_)
    repeat rewrite [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  have hZ : Measurable (f ∘ X) := by fun_prop
  rewrite [chain_rule'' μ hY hX, ← entropy_prod_comp hX μ f, ← h_joint,
    ← chain_rule'' μ hY (Measurable.prod (by exact hX) (by exact hZ))]
  exact entropy_submodular μ hY hX hZ
end _root_.ProbabilityTheory
end ProbabilityTheory

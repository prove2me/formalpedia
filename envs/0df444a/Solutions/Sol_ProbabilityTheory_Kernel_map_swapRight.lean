-- Prove2me | solution 1 for ProbabilityTheory.Kernel.map_swapRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:40.058833+00:00
-- url     : https://prove2.me/submissions/ce02cff0-b501-4d6f-a38f-1c466ce67623

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight


set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {α β γ δ ε : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {_ : MeasurableSpace ε}
variable {Ω S T : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace γ]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → β}
namespace ProbabilityTheory.Kernel
theorem _root_.solution (κ : Kernel α (β × γ)) {f : (γ × β) → δ} :
    map (swapRight κ) f = map κ (f ∘ Prod.swap) := by
  by_cases hf : Measurable f
  · rw [swapRight_eq, map_map _ measurable_swap hf]
  · have : ¬ Measurable (f ∘ Prod.swap) := by
      contrapose! hf
      exact hf.comp measurable_swap
    simp [map_of_not_measurable _ hf, map_of_not_measurable _ this]
end ProbabilityTheory.Kernel

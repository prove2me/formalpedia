-- Prove2me | solution 1 for ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:26.282613+00:00
-- url     : https://prove2.me/submissions/8f171bc2-4b7d-40b8-8160-99fc44ed195d

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight

attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse

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
theorem _root_.solution (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteRight (reverse κ)) = snd κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl
end ProbabilityTheory.Kernel

-- Prove2me | solution 1 for ProbabilityTheory.Kernel.swapRight_snd_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:36.10612+00:00
-- url     : https://prove2.me/submissions/ecb3fba6-32df-45cd-9705-4d62d72d66e4

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_snd
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_swapRight

attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse

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
    swapRight (snd (reverse κ)) = deleteRight κ := by
  rw [swapRight_eq, reverse_eq, deleteRight_eq, snd_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop)]
  rfl
end ProbabilityTheory.Kernel

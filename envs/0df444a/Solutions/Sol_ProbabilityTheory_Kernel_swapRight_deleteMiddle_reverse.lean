-- Prove2me | solution 1 for ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:50.731958+00:00
-- url     : https://prove2.me/submissions/e8228ba0-0b6a-413d-aaaa-ea513151ed0e

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
theorem _root_.solution (κ : Kernel α (β × γ × δ)) :
    swapRight (deleteMiddle (reverse κ)) = deleteMiddle κ := by
  rw [swapRight_eq, reverse_eq, deleteMiddle_eq, map_map _ (by fun_prop) (by fun_prop),
    map_map _ (by fun_prop) (by fun_prop), deleteMiddle_eq]
  rfl
end ProbabilityTheory.Kernel

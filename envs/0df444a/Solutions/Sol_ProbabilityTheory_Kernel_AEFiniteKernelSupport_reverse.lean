-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:35.756277+00:00
-- url     : https://prove2.me/submissions/9ca1b9b3-9b4e-4b01-90ec-8f49bdd3dd5c

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp

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
namespace _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
theorem _root_.solution
    [MeasurableSingletonClass S] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    {κ : Kernel T (S × β × γ)} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (reverse κ) μ := by
  rw [reverse_eq]
  apply hκ.map
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

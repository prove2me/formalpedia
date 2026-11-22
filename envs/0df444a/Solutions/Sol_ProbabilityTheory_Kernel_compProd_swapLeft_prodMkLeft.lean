-- Prove2me | solution 1 for ProbabilityTheory.Kernel.compProd_swapLeft_prodMkLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:34.464409+00:00
-- url     : https://prove2.me/submissions/d656cbbb-f094-4a37-8870-5a319fbb06c4

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  [MeasurableSpace T] [MeasurableSpace U]
open ProbabilityTheory.Kernel
variable [Countable U] [Nonempty U] [DiscreteMeasurableSpace U]
variable [Countable T] [MeasurableSingletonClass S] [MeasurableSingletonClass T]
namespace ProbabilityTheory.Kernel
theorem _root_.solution {α β γ : Type*} {mα : MeasurableSpace α} {mβ :
  MeasurableSpace β}
    {mγ : MeasurableSpace γ} (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    κ ⊗ₖ swapLeft (prodMkLeft β η) = κ ×ₖ η := by
  ext x s hs
  simp [compProd_apply hs, prod_apply' _ _ _ hs]
end ProbabilityTheory.Kernel

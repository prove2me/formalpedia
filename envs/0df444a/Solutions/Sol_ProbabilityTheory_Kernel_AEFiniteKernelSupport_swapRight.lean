-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.swapRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:31:38.014454+00:00
-- url     : https://prove2.me/submissions/a23e42b7-893b-437c-a78b-cd38d63e57bc

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
open Real MeasureTheory
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
namespace ProbabilityTheory.Kernel
namespace _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
theorem _root_.solution
    {κ : Kernel T (S × U)} {μ : Measure T}
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (swapRight κ) μ := by
  rw [swapRight_eq]
  apply hκ.map
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

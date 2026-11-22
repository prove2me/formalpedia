-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:31:18.84081+00:00
-- url     : https://prove2.me/submissions/65e8bebf-98f8-4fd5-95a8-c0dbe9f89555

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
    [MeasurableSingletonClass U] {κ : Kernel T (S × U)} {μ :
  Measure T}
    (hκ : AEFiniteKernelSupport κ μ) :
    AEFiniteKernelSupport (snd κ) μ := by
  rw [snd_eq]
  apply hκ.map
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

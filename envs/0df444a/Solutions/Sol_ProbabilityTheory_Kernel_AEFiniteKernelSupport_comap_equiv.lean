-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.comap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:14.309065+00:00
-- url     : https://prove2.me/submissions/30b7a2e9-1b7b-4458-877e-a2e489e54ab6

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
    [Countable U] [MeasurableSingletonClass U]
  {κ : Kernel T S} {μ : Measure T}
    (hκ : AEFiniteKernelSupport κ μ) (f : U ≃ᵐ T) :
    AEFiniteKernelSupport (Kernel.comap κ f f.measurable) (μ.comap f) := by
  rw [← @MeasurableEquiv.map_symm]
  rw [AEFiniteKernelSupport]
  simp_rw [Kernel.comap_apply]
  rw [ae_map_iff f.symm.measurable.aemeasurable]
  · simp only [MeasurableEquiv.apply_symm_apply]
    exact hκ
  · rw [Set.ofPred_exists]
    measurability
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

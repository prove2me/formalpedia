-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.prodMkRight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:57.642483+00:00
-- url     : https://prove2.me/submissions/bf3d0779-76a0-4ce9-beb2-235738d70bb9

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_finiteKernelSupport_mk
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_ae_eq_mk
public import Theorems.Thm_ProbabilityTheory_Kernel_aefiniteKernelSupport_iff

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
    [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U] [Countable U] {μ}
    {κ : Kernel T S} (hκ : AEFiniteKernelSupport κ μ)
    (ν : Measure U) [SFinite ν] :
    AEFiniteKernelSupport (prodMkRight U κ) (μ.prod ν) := by
  rw [aefiniteKernelSupport_iff]
  refine ⟨ProbabilityTheory.Kernel.prodMkRight U hκ.mk, hκ.finiteKernelSupport_mk.prodMkRight, ?_⟩
  rw [Filter.EventuallyEq]
  change ∀ᵐ (x : T × U) ∂(μ.prod ν),
    x ∈ {y | (ProbabilityTheory.Kernel.prodMkRight U hκ.mk) y = (ProbabilityTheory.Kernel.prodMkRight U κ) y}
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · filter_upwards [hκ.ae_eq_mk] with x hx
    simp [hx]
  · simp only [prodMkRight_apply, measurableSet_setOfPred]
    exact .of_discrete
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

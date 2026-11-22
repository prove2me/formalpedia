-- Prove2me | solution 1 for ProbabilityTheory.Kernel.condKernel_compProd_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:10.603942+00:00
-- url     : https://prove2.me/submissions/a0690760-b8e3-413a-a7e5-a336cb3c5b0f

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_apply
public import Theorems.Thm_MeasureTheory_lintegral_eq_tsum


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
theorem _root_.solution
    (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η] (μ : Measure T) :
    condKernel (κ ⊗ₖ η) =ᵐ[μ ⊗ₘ κ] η := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro x hx
  rw [condKernel_compProd_apply]
  rw [Measure.compProd_apply (.singleton _), lintegral_eq_tsum] at hx
  simp only [ne_eq, ENNReal.summable.tsum_eq_zero_iff, mul_eq_zero, not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  push Not at hy
  classical
  rw [← Prod.eta x, ← Set.singleton_prod_singleton, Set.mk_preimage_prod_right_eq_if] at hy
  simp only [ne_eq, Set.mem_singleton_iff] at hy
  by_cases hyx1 : y = x.1
  · simp_all
  · simp [hyx1] at hy
end ProbabilityTheory.Kernel

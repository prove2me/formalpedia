-- Prove2me | solution 1 for ProbabilityTheory.Kernel.FiniteKernelSupport.compProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:35:23.273858+00:00
-- url     : https://prove2.me/submissions/32914878-c873-4557-bb8f-9b6d920e761f

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_local_support_of_finiteKernelSupport
public import Theorems.Thm_MeasureTheory_lintegral_eq_setLIntegral
public import Theorems.Thm_MeasureTheory_setLIntegral_eq_sum


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
namespace _root_.ProbabilityTheory.Kernel.FiniteKernelSupport
theorem _root_.solution
    [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U}
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    FiniteKernelSupport (κ ⊗ₖ η) := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  intro t
  rcases hκ t with ⟨A, hA⟩
  rcases (local_support_of_finiteKernelSupport hη ({t} ×ˢ A)) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Kernel.compProd_apply (by measurability), lintegral_eq_setLIntegral hA,
    setLIntegral_eq_sum]
  apply Finset.sum_eq_zero
  intro s hs
  simp only [Finset.coe_product, Set.preimage_compl, mul_eq_zero]
  right
  refine measure_mono_null ?_ (hB (t, s) (by simp [hs]))
  intro u; simp; tauto
end _root_.ProbabilityTheory.Kernel.FiniteKernelSupport
end ProbabilityTheory.Kernel

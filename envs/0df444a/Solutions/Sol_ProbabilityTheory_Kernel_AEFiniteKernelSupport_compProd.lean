-- Prove2me | solution 1 for ProbabilityTheory.Kernel.AEFiniteKernelSupport.compProd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:40.540465+00:00
-- url     : https://prove2.me/submissions/1b8d6495-53a0-4496-91fe-f626e5580522

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_compProd_congr_ae
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_finiteKernelSupport_mk
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_ae_eq_mk
public import Theorems.Thm_ProbabilityTheory_Kernel_aefiniteKernelSupport_iff
public import Theorems.Thm_ProbabilityTheory_Kernel_FiniteKernelSupport_compProd

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
    [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
    {κ : Kernel T S} {η : Kernel (T × S) U} {μ : Measure T} [SFinite μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    AEFiniteKernelSupport (κ ⊗ₖ η) μ := by
  by_cases hκ' : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel_left _ _ hκ']
  by_cases hη' : IsSFiniteKernel η; swap
  · simp [compProd_of_not_isSFiniteKernel_right _ _ hη']
  rw [aefiniteKernelSupport_iff]
  refine ⟨hκ.mk ⊗ₖ hη.mk, ?_, ?_⟩
  · exact hκ.finiteKernelSupport_mk.compProd hη.finiteKernelSupport_mk
  · have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
    refine compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm
end _root_.ProbabilityTheory.Kernel.AEFiniteKernelSupport
end ProbabilityTheory.Kernel

-- Prove2me | solution 1 for ProbabilityTheory.Kernel.aefiniteKernelSupport_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:21.513812+00:00
-- url     : https://prove2.me/submissions/d3cf1966-6b74-4d0a-842c-0d43fd610127

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_finiteKernelSupport_mk
public import Theorems.Thm_ProbabilityTheory_Kernel_AEFiniteKernelSupport_ae_eq_mk

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
variable [Countable T] [MeasurableSingletonClass T] {μ : Measure T}
namespace ProbabilityTheory.Kernel
theorem _root_.solution [MeasurableSingletonClass S] {κ : Kernel T S} {μ : Measure T} :
    AEFiniteKernelSupport κ μ ↔ ∃ κ' : Kernel T S,
      FiniteKernelSupport κ' ∧ κ' =ᵐ[μ] κ := by
  refine ⟨fun h ↦ ⟨h.mk, h.finiteKernelSupport_mk, h.ae_eq_mk.symm⟩, fun ⟨κ', hκ',
    h_eq⟩ ↦ ?_⟩
  filter_upwards [h_eq] with x hx
  rw [← hx]
  exact hκ' x
end ProbabilityTheory.Kernel

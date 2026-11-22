-- Prove2me | solution 1 for ProbabilityTheory.Kernel.condKernel_prod_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:58.315797+00:00
-- url     : https://prove2.me/submissions/aed34f72-7865-4fd3-9522-45f2e8d50500

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_ae_eq
public import Theorems.Thm_ProbabilityTheory_Kernel_compProd_swapLeft_prodMkLeft

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
theorem _root_.solution (κ : Kernel T S) [IsFiniteKernel κ] {μ}
    (η : Kernel T U) [IsMarkovKernel η] :
    condKernel (κ ×ₖ η) =ᵐ[μ ⊗ₘ κ] prodMkRight S η := by
  simp_rw [← compProd_swapLeft_prodMkLeft]
  exact condKernel_compProd_ae_eq _ _ _
end ProbabilityTheory.Kernel

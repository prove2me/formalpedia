-- Prove2me | solution 1 for ProbabilityTheory.Kernel.ae_eq_condKernel_of_compProd_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:03.951234+00:00
-- url     : https://prove2.me/submissions/8bc6b77f-4f02-46f6-9016-04f3fbb9818b

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_ProbabilityTheory_Kernel_condKernel_compProd_ae_eq

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
theorem _root_.solution (κ : Kernel T (S × U)) [IsFiniteKernel κ] {μ}
    (η : Kernel (T × S) U) [IsMarkovKernel η] (h : fst κ ⊗ₖ η = κ) :
    η =ᵐ[μ ⊗ₘ fst κ] condKernel κ := by
  have : condKernel κ = condKernel ((fst κ) ⊗ₖ η) := by congr; exact h.symm
  rw [this]
  exact (condKernel_compProd_ae_eq _ _ _).symm
end ProbabilityTheory.Kernel

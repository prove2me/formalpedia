-- Prove2me | solution 1 for P2M_ProbabilityTheory_Kernel_condKernel_compProd_apply__368aa807565a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:49.802094+00:00
-- url     : https://prove2.me/submissions/47a0e419-6cea-4bd6-b6e8-7393b1652326

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
public import Theorems.Thm_ZhangYeungImport_MeasureTheory_lintegral_eq_single


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
namespace ProbabilityTheory.Kernel
theorem _root_.solution (κ : Kernel T S) [IsFiniteKernel κ]
    (η : Kernel (T × S) U) [IsMarkovKernel η]
    (x : T × S) (hx : κ x.1 {x.2} ≠ 0) {s : Set U} (hs : MeasurableSet s) :
    condKernel (κ ⊗ₖ η) x s = η x s := by
  have hx' : (κ ⊗ₖ η) x.1 (Prod.fst ⁻¹' {x.2}) ≠ 0 := by
    rwa [compProd_preimage_fst (.singleton _)]
  rw [condKernel_apply' _ _ hx', compProd_apply ((measurableSet_singleton _).prod hs),
    Kernel.compProd_apply, lintegral_eq_single _ x.2, lintegral_eq_single _ x.2]
  · simp [Set.preimage_preimage, mul_comm]
    simp [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top (κ x.1) {x.2})]
  · simp_all
  · intro b hb
    simp [hb, Set.preimage_preimage]
  · measurability
end ProbabilityTheory.Kernel

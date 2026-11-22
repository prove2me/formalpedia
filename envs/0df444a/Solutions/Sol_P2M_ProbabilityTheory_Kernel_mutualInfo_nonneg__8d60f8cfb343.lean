-- Prove2me | solution 1 for P2M_ProbabilityTheory_Kernel_mutualInfo_nonneg__8d60f8cfb343
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:49:29.475188+00:00
-- url     : https://prove2.me/submissions/1f509af2-b3c6-4151-9c68-5afb2e8ab27e

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Composition_Comp
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Real
open scoped ENNReal NNReal Topology ProbabilityTheory
open ProbabilityTheory ProbabilityTheory.Kernel
variable {Ω S T U V : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U] [MeasurableSpace V]
  {κ : Kernel T S} {μ : Measure T} {X : Ω → S} {Y : Ω → U}
variable [MeasurableSingletonClass S] [MeasurableSingletonClass U]
variable [MeasurableSingletonClass T]
namespace ProbabilityTheory.Kernel
theorem _root_.solution {κ : Kernel T (S × U)} {μ : Measure T} [IsFiniteMeasure μ]
    [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    0 ≤ Ik[κ, μ] := by
  simp_rw [mutualInfo, entropy, integral_eq_setIntegral (ae_mem_support μ),
    setIntegral_finset _ .finset, smul_eq_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  simp_rw [← mul_add, ← mul_sub, fst_apply, snd_apply]
  have (x : T) : FiniteSupport (κ x) := ⟨hκ x⟩
  exact Finset.sum_nonneg fun x _ ↦ mul_nonneg ENNReal.toReal_nonneg measureMutualInfo_nonneg
end ProbabilityTheory.Kernel

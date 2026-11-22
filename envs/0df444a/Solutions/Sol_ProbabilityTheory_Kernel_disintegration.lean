-- Prove2me | solution 1 for ProbabilityTheory.Kernel.disintegration
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:48.012861+00:00
-- url     : https://prove2.me/submissions/aef8a970-e942-471d-b095-332e02298ccc

module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.CondDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Integral_Lebesgue_Countable
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Kernel_Disintegration
public import Theorems.Thm_P2M_ProbabilityTheory_Kernel_condKernel_apply__e1c6db4f1898
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
namespace ProbabilityTheory.Kernel
theorem _root_.solution (κ : Kernel T (S × U)) [IsFiniteKernel κ] :
    κ = (Kernel.fst κ) ⊗ₖ (condKernel κ) := by
  ext x s hs
  rw [compProd_apply hs, lintegral_fst]
  swap; · exact measurable_kernel_prodMk_left' hs x
  rw [lintegral_eq_tsum, ENNReal.tsum_prod']
  change κ x s = ∑' a : S, ∑' b : U, κ x {(a, b)} * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
  simp_rw [ENNReal.tsum_mul_right, ← measure_preimage_fst_singleton_eq_tsum (κ x)]
  have : ∑' a : S, (κ x (Prod.fst ⁻¹' {a})) * condKernel κ (x, a) (Prod.mk a ⁻¹' s)
      = ∑' a : S, κ x (Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s}) := by
    congr with a
    by_cases ha : κ x (Prod.fst ⁻¹' {a}) = 0
    · simp only [ha, zero_mul]
      exact (measure_mono_null Set.inter_subset_left ha).symm
    · rw [condKernel_apply' κ _ ha, ← mul_assoc,
      ENNReal.mul_inv_cancel ha (measure_ne_top _ _), one_mul]
      congr
  simp_rw [this]
  have : ⋃ a, Prod.fst ⁻¹' {a} ∩ {su | (a, su.2) ∈ s} = s := by ext a; simp
  conv_lhs => rw [← this]
  rw [measure_iUnion]
  · intro a a' haa'
    rw [Function.onFun, Set.disjoint_iff]
    intro su
    simp_all
  · refine fun _ ↦ (measurable_fst (.singleton _)).inter ?_
    exact measurable_prodMk_left.comp measurable_snd hs
end ProbabilityTheory.Kernel

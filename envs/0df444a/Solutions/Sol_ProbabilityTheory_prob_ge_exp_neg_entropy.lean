-- Prove2me | solution 1 for ProbabilityTheory.prob_ge_exp_neg_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:03:48.685527+00:00
-- url     : https://prove2.me/submissions/f92f28a2-a4f5-4efc-a8e4-ba0782940e84

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Kernel_MutualInfo
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Uniform
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Measure_Prod
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Entropy_Basic
public import Theorems.Thm_ProbabilityTheory_entropy_eq_sum_finset
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_compProd_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_const
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_deterministic
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prod
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkLeft
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_prodMkRight
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_kernel
public import Theorems.Thm_ProbabilityTheory_Kernel_entropy_zero_measure
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteMiddle_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_deleteRight_reverse
public import Theorems.Thm_ProbabilityTheory_Kernel_swapRight_snd_reverse
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] P2M_MeasureTheory_Measure_dirac_real_apply__5ab26a8900c7
attribute [local simp] ProbabilityTheory.Kernel.entropy_compProd_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_const
attribute [local simp] ProbabilityTheory.Kernel.entropy_deterministic
attribute [local simp] ProbabilityTheory.Kernel.entropy_prod
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkLeft
attribute [local simp] ProbabilityTheory.Kernel.entropy_prodMkRight
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_kernel
attribute [local simp] ProbabilityTheory.Kernel.entropy_zero_measure
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteMiddle_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_deleteRight_reverse
attribute [local simp] ProbabilityTheory.Kernel.swapRight_snd_reverse
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq



set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure Real
open scoped ENNReal NNReal Topology ProbabilityTheory ZhangYeungPFR
open ProbabilityTheory
variable {Ω S T U T' : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}
open Set
open Function
namespace ProbabilityTheory
theorem _root_.solution [MeasurableSingletonClass S] (X : Ω → S) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hX : Measurable X) [hX' : FiniteRange X] :
    ∃ s : S, μ Set.univ * (rexp (- H[X; μ])).toNNReal ≤ μ.map X {s} := by
  have : Nonempty Ω := μ.nonempty_of_neZero
  have : Nonempty S := Nonempty.map X (by infer_instance)
  let μS := μ.map X
  let μs s := μS {s}
  rcases finiteSupport_of_finiteRange (X := X) with ⟨A, hA⟩
  let S_nonzero := A.filter (fun s ↦ μs s ≠ 0)
  set norm := μS A with rw_norm
  have h_norm : norm = μ Set.univ := by
    have := measure_add_measure_compl (μ := μS) (s := A) (Finset.measurableSet _)
    change μS (A : Set S)ᶜ = 0 at hA
    rw [hA, add_zero] at this
    simp [norm, μS, this, Measure.map_apply hX MeasurableSet.univ]
  let pdf_nn s := norm⁻¹ * μs s
  let pdf s := (pdf_nn s).toReal
  let neg_log_pdf s := -log (pdf s)
  rcases Finset.eq_empty_or_nonempty S_nonzero with h_empty | h_nonempty
  · have h_norm_zero : μ Set.univ = 0 := by
      have h : ∀ s ∈ A, μs s ≠ 0 → μs s ≠ 0 := fun _ _ h ↦ h
      rw [← h_norm, rw_norm, ← sum_measure_singleton, ← Finset.sum_filter_of_ne h,
        show Finset.filter _ _ = S_nonzero from rfl, h_empty, show Finset.sum ∅ μs = 0 from rfl]
    use Classical.arbitrary (α := S)
    simp [h_norm_zero]
  rcases exists_or_forall_not (fun s ↦ μ.map X {s} = ∞) with h_infty | h_finite
  · simp_all
  rcases eq_zero_or_neZero μ with h_zero_measure | _
  · use Classical.arbitrary (α := S)
    rw [h_zero_measure, show (0 : Measure Ω) _ = 0 from rfl, zero_mul]
    exact zero_le
  have h_norm_pos : 0 < norm := by
    rw [h_norm, Measure.measure_univ_pos]
    exact NeZero.ne μ
  have h_norm_finite : norm < ∞ := by
    simp_all
  have h_invinvnorm_finite : norm⁻¹⁻¹ ≠ ∞ := by
    simp_all
  have h_invnorm_ne_zero : norm⁻¹ ≠ 0 := ENNReal.inv_ne_top.mp h_invinvnorm_finite
  have h_invnorm_finite : norm⁻¹ ≠ ∞ := by
    rw [← ENNReal.inv_ne_zero, inv_inv]
    exact h_norm_pos.ne'
  have h_pdf_finite : ∀ s,
    pdf_nn s ≠ ∞ := fun s ↦ ENNReal.mul_ne_top h_invnorm_finite (h_finite s)
  have h_norm_cancel : norm * norm⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h_norm_pos.ne' h_norm_finite.ne
  have h_pdf1 : (∑ s ∈ A, pdf s) = 1 := by
    rw [← ENNReal.toReal_sum (fun s _ ↦ h_pdf_finite s), ← Finset.mul_sum,
      sum_measure_singleton, mul_comm, h_norm_cancel, ENNReal.toReal_one]
  let ⟨s_max, hs, h_min⟩ := Finset.exists_min_image S_nonzero neg_log_pdf h_nonempty
  have h_pdf_s_max_pos : 0 < pdf s_max := by
    rw [Finset.mem_filter] at hs
    have h_nonzero : pdf s_max ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨mul_ne_zero h_invnorm_ne_zero hs.2, ENNReal.mul_ne_top h_invnorm_finite (h_finite s_max)⟩
    exact LE.le.lt_of_ne ENNReal.toReal_nonneg h_nonzero.symm
  use s_max
  rw [← h_norm, ← one_mul (μ.map X _), ← h_norm_cancel, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (le_of_lt h_norm_pos)
  change ENNReal.ofReal (rexp (-H[X; μ])) ≤ pdf_nn s_max
  rw [ENNReal.ofReal_le_iff_le_toReal (h_pdf_finite _),
    show (pdf_nn _).toReal = pdf _ from rfl, ← Real.exp_log h_pdf_s_max_pos]
  apply exp_monotone
  rw [neg_le, ← one_mul (-log _), ← h_pdf1, Finset.sum_mul]
  let g_lhs s := pdf s * neg_log_pdf s_max
  let g_rhs s := -pdf s * log (pdf s)
  suffices ∑ s ∈ A, g_lhs s ≤ ∑ s ∈ A, g_rhs s by
    refine le_of_le_of_eq this ?_
    rw [entropy_eq_sum_finset hA]
    congr with s
    simp only [negMulLog, neg_mul, ENNReal.toReal_mul, neg_inj, g_rhs, pdf, pdf_nn]
    simp at h_norm
    simp [h_norm, μs, μS, Measure.real]
  have h_lhs : ∀ s, μs s = 0 → g_lhs s = 0 := by {intros _ h; simp [g_lhs, pdf, pdf_nn, h]}
  have h_rhs : ∀ s, μs s = 0 → g_rhs s = 0 := by {intros _ h; simp [g_rhs, pdf, pdf_nn, h]}
  rw [← Finset.sum_filter_of_ne (fun s _ ↦ (h_lhs s).mt),
    ← Finset.sum_filter_of_ne (fun s _ ↦ (h_rhs s).mt)]
  apply Finset.sum_le_sum
  intros s h_s
  rw [show g_lhs s = _ * _ from rfl, show g_rhs s = _ * _ from rfl, neg_mul_comm]
  exact mul_le_mul_of_nonneg_left (h_min s h_s) ENNReal.toReal_nonneg
end ProbabilityTheory

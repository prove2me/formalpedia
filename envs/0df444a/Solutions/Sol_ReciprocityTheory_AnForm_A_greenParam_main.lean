-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.greenParam_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:38.226483+00:00
-- url     : https://prove2.me/submissions/4828f6ed-eaa7-4cca-a1ec-520ccba88f04

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_GreenPolar
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Theorems.Thm_ReciprocityTheory_AnForm_A_exists_R_of_compact
import Theorems.Thm_ReciprocityTheory_AnForm_A_greenParamFiber_main
import Theorems.Thm_ReciprocityTheory_AnForm_A_lap_fiber
import Theorems.Thm_ReciprocityTheory_AnForm_A_GreenFunction_integrable_log_norm_ball


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Filter Topology InnerProductSpace
open scoped Laplacian
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GreenFunction
noncomputable section
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution : GreenParamStatement := by
  intro E _ _ _ _ _ μ _ u hu hc
  obtain ⟨R, hR0, hR⟩ := exists_R_of_compact hc
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set G : ℂ × E → ℝ := fun q => fderiv ℝ (fderiv ℝ u) q (1, 0) (1, 0)
      + fderiv ℝ (fderiv ℝ u) q (Complex.I, 0) (Complex.I, 0) with hG
  have hGc : Continuous G := by fun_prop
  have hF : (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1) =
      fun q => Real.log ‖q.1‖ * G q := by
    funext q; rw [lap_fiber hu]
  have hG0 : ∀ q, q ∉ tsupport u → G q = 0 := fun q hq => by
    have : fderiv ℝ (fderiv ℝ u) q = 0 := by
      by_contra h
      exact hq (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ
        (subset_tsupport (fderiv ℝ (fderiv ℝ u)) h)))
    simp [G, this]
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hGc.continuousOn
  have hint : Integrable (fun q : ℂ × E => Real.log ‖q.1‖ * Δ (fun w : ℂ => u (w, q.2)) q.1)
      ((volume : Measure ℂ).prod μ) := by
    rw [hF]
    have hg1 : Integrable (fun z : ℂ => max C 0 * (Iic R).indicator (fun t => ‖Real.log t‖) ‖z‖) :=
      (integrable_log_norm_ball hR0).const_mul _
    have hg2 : Integrable (fun p : E => (Metric.closedBall (0 : E) R).indicator (fun _ => (1 : ℝ)) p) μ :=
      (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
        (integrableOn_const (isCompact_closedBall 0 R).measure_lt_top.ne)
    refine (hg1.mul_prod hg2).mono'
      ((Real.measurable_log.comp (measurable_norm.comp measurable_fst)).aestronglyMeasurable.mul
        hGc.aestronglyMeasurable) (Eventually.of_forall fun q => ?_)
    by_cases hq : q ∈ tsupport u
    · have hn := hR q hq
      have h1 : ‖q.1‖ ∈ Iic R := by simp only [mem_Iic]; linarith [norm_fst_le q]
      have h2 : q.2 ∈ Metric.closedBall (0 : E) R := by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith [norm_snd_le q]
      simp only [indicator_of_mem h1, indicator_of_mem h2, mul_one, norm_mul]
      rw [mul_comm (max C 0)]
      exact mul_le_mul_of_nonneg_left ((hC q hq).trans (le_max_left _ _)) (norm_nonneg _)
    · rw [hG0 q hq, mul_zero, norm_zero]
      exact mul_nonneg (mul_nonneg (le_max_right _ _)
        (indicator_nonneg (fun _ _ => norm_nonneg _) _))
        (indicator_nonneg (fun _ _ => zero_le_one) _)
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  simp only
  rw [integral_congr_ae (Eventually.of_forall fun p => (greenParamFiber_main E u hu hc p).2)]
  exact integral_const_mul _ _
end ReciprocityTheory.AnForm.A

-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.disc_mean_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:36:34.977071+00:00
-- url     : https://prove2.me/submissions/1f13217f-f01d-425d-baf5-672b6730ef7a

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_integral_ball_polar
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_pgds_circle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
open Set
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {R r : ℝ} (hr : 0 < r) (hrR : r < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) (w : ℝ → ℝ) (hwc : Continuous w)
    (hw : ∀ s, 0 ≤ w s) :
    ‖g 0‖ ^ 2 * ∫ z in Metric.ball (0 : ℂ) r, w ‖z‖ ≤
      ∫ z in Metric.ball (0 : ℂ) r, ‖g z‖ ^ 2 * w ‖z‖ := by
  have hgc : ContinuousOn g (Metric.closedBall 0 r) :=
    hg.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  obtain ⟨hiR, eR⟩ := pgds_integral_ball_polar (r := r) (fun z => ‖g z‖ ^ 2 * w ‖z‖)
    ((hgc.norm.pow 2).mul (hwc.comp continuous_norm).continuousOn)
  obtain ⟨-, eL⟩ := pgds_integral_ball_polar (r := r) (fun z => w ‖z‖)
    (hwc.comp continuous_norm).continuousOn
  rw [eL, eR, ← integral_const_mul]
  have hI : Integrable (fun p : ℝ × ℝ => p.1 * (‖g (Complex.polarCoord.symm p)‖ ^ 2 *
      w ‖Complex.polarCoord.symm p‖))
      ((volume.restrict (Ioo 0 r)).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hiR
  refine integral_mono_of_nonneg ?_ hI.integral_prod_left ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_Ioo
      fun θ _ => mul_nonneg hs.1.le (hw _))
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have key := pgds_circle hs.1 (hs.2.trans hrR) g hg
    simp only [Complex.norm_polarCoord_symm, abs_of_pos hs.1]
    rw [setIntegral_const]
    simp only [measureReal_def, Real.volume_Ioo, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    have e : ∀ θ : ℝ, s * (‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 * w s) =
        (s * w s) * ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := fun θ => by ring
    simp only [e]
    rw [integral_const_mul]
    have hsw : 0 ≤ s * w s := mul_nonneg hs.1.le (hw s)
    have := mul_le_mul_of_nonneg_left key hsw
    nlinarith
end ReciprocityTheory.GeometryOfNumbersTheory

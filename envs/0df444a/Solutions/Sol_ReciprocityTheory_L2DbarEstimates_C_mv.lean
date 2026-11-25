-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:43:57.394819+00:00
-- url     : https://prove2.me/submissions/39c4d720-2035-4970-9809-147723da4c33

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_rotAbout_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_rotAbout_mem_ball_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_setLIntegral_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_exp_mul_I_eq_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuousOn_comp_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_circle_mean_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution : MVStatement := by
  intro n c R u r hu hr
  have hT1 := norm_exp_mul_I_eq_one
  have hrot : ∀ θ : ℝ, ∫⁻ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ =
        ∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖ := by
    intro θ
    have h := setLIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z‖ₑ ^ 2 * r ‖z - c‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hmeas : AEMeasurable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    rw [Measure.prod_restrict]
    have h1 := ((continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aemeasurable
      (μ := volume.prod volume) (measurableSet_Ioc.prod measurableSet_ball)).enorm.pow_const 2
    have h2 : Measurable fun p : ℝ × V n => r ‖p.2 - c‖ :=
      hr.comp ((measurable_snd.sub_const c).norm)
    exact h1.mul h2.aemeasurable
  have hvol : volume (Ioc (0 : ℝ) (2 * Real.pi)) = ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioc, sub_zero]
  have key : (∫⁻ z in ball c R, ‖u z‖ₑ ^ 2 * r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi) =
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← hvol, ← setLIntegral_const, ← lintegral_lintegral_swap hmeas]
    exact lintegral_congr fun θ => (hrot θ).symm
  have hmr : Measurable fun z : V n => r ‖z - c‖ := hr.comp (measurable_id.sub_const c).norm
  have low : ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ ≤
      ∫⁻ z in ball c R, ∫⁻ θ in Ioc 0 (2 * Real.pi),
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 * r ‖z - c‖ := by
    rw [← lintegral_const_mul _ hmr]
    refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcz : Continuous fun θ : ℝ => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) :=
      hu.continuousOn.comp_continuous (by unfold rotAbout; fun_prop)
        (fun θ => (rotAbout_mem_ball_iff c (hT1 θ) R z).2 hz)
    have hm : Measurable fun θ : ℝ =>
        ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z)‖ₑ ^ 2 :=
      hcz.measurable.enorm.pow_const 2
    rw [lintegral_mul_const _ hm]
    gcongr
    exact circle_mean_sq hu hw
  have h0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  refine (ENNReal.mul_le_mul_iff_left h0 ENNReal.ofReal_ne_top).1 ?_
  calc ‖u c‖ₑ ^ 2 * (∫⁻ z in ball c R, r ‖z - c‖) * ENNReal.ofReal (2 * Real.pi)
      = ‖u c‖ₑ ^ 2 * ENNReal.ofReal (2 * Real.pi) * ∫⁻ z in ball c R, r ‖z - c‖ := by ring
    _ ≤ _ := low
    _ = _ := key.symm
end ReciprocityTheory.L2DbarEstimates.C

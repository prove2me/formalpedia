-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.mvEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:45.410792+00:00
-- url     : https://prove2.me/submissions/3c3debb3-ce8c-4b62-9dd2-2d5381a29b11

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_Circle
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_rotAbout_sub
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_setIntegral_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_integrableOn_rotAbout_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_norm_exp_mul_I_eq_one
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_continuousOn_comp_rotAbout
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_circle_mean


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
theorem _root_.solution : MVEqStatement := by
  intro n c R u k hu hk hF
  have hT1 := norm_exp_mul_I_eq_one
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := Real.two_pi_pos.le
  have hrot : ∀ θ : ℝ, ∫ z in ball c R,
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) := by
    intro θ
    have h := setIntegral_rotAbout c (hT1 θ) R (fun z => u z * (k ‖z - c‖ : ℂ))
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hrotN : ∀ θ : ℝ, ∫ z in ball c R,
      ‖u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ)‖ =
        ∫ z in ball c R, ‖u z * (k ‖z - c‖ : ℂ)‖ := by
    intro θ
    have h := setIntegral_rotAbout c (hT1 θ) R (fun z => ‖u z * (k ‖z - c‖ : ℂ)‖)
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h
  have hrotI : ∀ θ : ℝ, IntegrableOn
      (fun z => u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ)) (ball c R) := by
    intro θ
    have h := integrableOn_rotAbout_iff c (hT1 θ) R (fun z => u z * (k ‖z - c‖ : ℂ))
    simp only [rotAbout_sub c (hT1 θ)] at h
    exact h.2 hF
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2) * (k ‖p.2 - c‖ : ℂ))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    have h1 : AEStronglyMeasurable
        (fun p : ℝ × V n => u (rotAbout c (Complex.exp ((p.1 : ℂ) * I)) p.2))
        ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
      rw [Measure.prod_restrict]
      exact (continuousOn_comp_rotAbout hu (Ioc 0 (2 * Real.pi))).aestronglyMeasurable
        (measurableSet_Ioc.prod measurableSet_ball)
    exact h1.mul hk.aestronglyMeasurable.comp_snd
  have hint : Integrable (Function.uncurry fun (θ : ℝ) (z : V n) =>
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ))
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod (volume.restrict (ball c R))) := by
    refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall hrotI, ?_⟩
    have hc0 : Integrable (fun _ : ℝ => ∫ z in ball c R, ‖u z * (k ‖z - c‖ : ℂ)‖)
        (volume.restrict (Ioc 0 (2 * Real.pi))) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    exact hc0.congr (Eventually.of_forall fun θ => (hrotN θ).symm)
  have hswap := integral_integral_swap hint
  have hL : ∫ θ in Ioc 0 (2 * Real.pi), ∫ z in ball c R,
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) := by
    simp only [hrot]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le hpi, sub_zero, Complex.real_smul]
  have hR : ∫ z in ball c R, ∫ θ in Ioc 0 (2 * Real.pi),
      u (rotAbout c (Complex.exp ((θ : ℂ) * I)) z) * (k ‖z - c‖ : ℂ) =
        ((2 * Real.pi : ℝ) : ℂ) * u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
    have hw : ‖z - c‖ < R := by rw [mem_ball, dist_eq_norm] at hz; exact hz
    have hcm := circle_mean hu hw
    simp only [rotAbout]
    rw [integral_mul_const, ← intervalIntegral.integral_of_le hpi, hcm]
  have h2 : ((2 * Real.pi : ℝ) : ℂ) * ∫ z in ball c R, u z * (k ‖z - c‖ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (u c * ∫ z in ball c R, (k ‖z - c‖ : ℂ)) := by
    rw [← hL, hswap, hR, mul_assoc]
  have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  exact mul_left_cancel₀ hne h2
end ReciprocityTheory.L2DbarEstimates.C

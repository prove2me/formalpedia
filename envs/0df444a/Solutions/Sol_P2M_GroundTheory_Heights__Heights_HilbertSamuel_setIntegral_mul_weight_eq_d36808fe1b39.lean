-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_mul_weight_eq_d36808fe1b39
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:41.896617+00:00
-- url     : https://prove2.me/submissions/612df490-099d-4f40-9240-85b102b0266c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PolydiscMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_setIntegral_circle_smul_19f89149fa7e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {D : ℕ} {ρ : ℝ} {g : (Fin D → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g (closedBall 0 ρ)) {w : (Fin D → ℂ) → ℝ} (hw : Continuous w)
    (hrot : ∀ (u : Circle) z, w ((u : ℂ) • z) = w z) :
    ∫ z in closedBall (0 : Fin D → ℂ) ρ, g z * (w z : ℂ) =
      g 0 * ∫ z in closedBall (0 : Fin D → ℂ) ρ, (w z : ℂ) := by
  set B := closedBall (0 : Fin D → ℂ) ρ with hBdef
  set F : ℝ → (Fin D → ℂ) → ℂ := fun θ z => g (Complex.exp (θ * Complex.I) • z) * (w z : ℂ)
    with hFdef
  have hnorm : ∀ (θ : ℝ) (z : Fin D → ℂ), ‖Complex.exp (θ * Complex.I) • z‖ = ‖z‖ := by
    intro θ z
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

  have hrotI : ∀ θ : ℝ, ∫ z in B, F θ z = ∫ z in B, g z * (w z : ℂ) := by
    intro θ
    have := setIntegral_circle_smul (Circle.exp θ) ρ (fun z => g z * (w z : ℂ))
    simp only [hrot] at this
    simp only [Circle.coe_exp] at this
    exact this

  have hmean : ∀ z ∈ B, ∫ θ in (0 : ℝ)..2 * π, g (Complex.exp (θ * Complex.I) • z) =
      (2 * π) • g 0 := by
    intro z hz
    set h : ℂ → ℂ := fun ζ => g (ζ • z) with hhdef
    have hh : AnalyticOnNhd ℂ h (closedBall 0 1) := by
      intro ζ hζ
      have hmem : ζ • z ∈ B := by
        rw [mem_closedBall_zero_iff] at hz hζ ⊢
        rw [norm_smul]
        exact (mul_le_of_le_one_left (norm_nonneg _) hζ).trans hz
      have hA : AnalyticAt ℂ (fun ζ : ℂ => ζ • z) ζ :=
        ((ContinuousLinearMap.id ℂ ℂ).smulRight z).analyticAt ζ
      exact (hg (ζ • z) hmem).comp_of_eq hA rfl
    have hc : circleAverage h 0 1 = h 0 := by
      apply DiffContOnCl.circleAverage
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
      exact hh.differentiableOn
    have e : ∀ θ : ℝ, circleMap 0 1 θ = Complex.exp (θ * Complex.I) := by
      intro θ
      simp [circleMap]
    rw [circleAverage_def] at hc
    simp only [hhdef, e, zero_smul] at hc
    rw [← hc, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

  have hcont : ContinuousOn (Function.uncurry F) (Icc 0 (2 * π) ×ˢ B) := by
    have hmaps : MapsTo (fun p : ℝ × (Fin D → ℂ) => Complex.exp (p.1 * Complex.I) • p.2)
        (Icc 0 (2 * π) ×ˢ B) B := by
      intro p hp
      simp only [hBdef, mem_closedBall_zero_iff, hnorm]
      exact mem_closedBall_zero_iff.mp hp.2
    exact (hg.continuousOn.comp (by fun_prop) hmaps).mul (by fun_prop)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict B)) := by
    rw [Measure.prod_restrict]
    exact (hcont.integrableOn_compact (μ := volume.prod volume)
      (isCompact_Icc.prod (isCompact_closedBall 0 ρ))).mono_set
      (prod_mono Ioc_subset_Icc_self subset_rfl)
  have hswap := integral_integral_swap hint
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  apply smul_right_injective ℂ h2pi
  simp only
  calc (2 * π) • ∫ z in B, g z * (w z : ℂ)
      = ∫ θ in Ioc 0 (2 * π), ∫ z in B, F θ z := by
        simp_rw [hrotI]
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal (by positivity)]
    _ = ∫ z in B, ∫ θ in Ioc 0 (2 * π), F θ z := hswap
    _ = ∫ z in B, ((2 * π) • g 0) * (w z : ℂ) := by
        refine setIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
        simp only [hFdef]
        rw [integral_mul_const, ← intervalIntegral.integral_of_le (by positivity), hmean z hz]
    _ = (2 * π) • (g 0 * ∫ z in B, (w z : ℂ)) := by
        rw [integral_const_mul, smul_mul_assoc]
end GroundTheory.Heights₂.Heights.HilbertSamuel

-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.morse_normal_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:14.827706+00:00
-- url     : https://prove2.me/submissions/8cd8dfb0-c7db-4570-9a55-4dc2f92c8db7

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_PolydiscSt
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_MorseNormSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_discI_scale
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_polydisc_gauss_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Filter Topology
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} {ρ₀ C : ℝ} (hC : 0 ≤ C) (lam : Fin D → ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (φ ν : (Fin D → ℂ) → ℝ)
    (hφc : ContinuousOn φ (Metric.ball 0 ρ₀)) (hνc : ContinuousOn ν (Metric.ball 0 ρ₀))
    (hφ : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, φ z ≤ ∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3)
    (hν : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀, 1 - C * ‖z‖ ≤ ν z)
    (f : (Fin D → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ₀))
    (n : ℕ) (hn : 0 < n) (R : ℝ) (hR : 0 < R) (hRn : R / Real.sqrt n < ρ₀)
    (hCR : C * (R / Real.sqrt n) < 1) :
    ‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D) *
        (Real.exp (-(C * R ^ 3 / Real.sqrt n)) * (1 - C * (R / Real.sqrt n))) ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) (R / Real.sqrt n),
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
  set s := Real.sqrt (n : ℝ) with hs_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.mpr hn'
  have hss : s * s = n := Real.mul_self_sqrt hn'.le
  set r := R / s with hr_def
  have hr : 0 < r := div_pos hR hs
  set K := Real.exp (-(C * R ^ 3 / s)) * (1 - C * r) with hK
  have hK0 : 0 ≤ K := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hsub : Metric.closedBall (0 : Fin D → ℂ) r ⊆ Metric.ball 0 ρ₀ :=
    Metric.closedBall_subset_ball hRn

  have hcont : ContinuousOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
      (Metric.closedBall (0 : Fin D → ℂ) r) := by
    have h1 : ContinuousOn f (Metric.closedBall (0 : Fin D → ℂ) r) := hf.continuousOn.mono hsub
    have h2 : ContinuousOn φ (Metric.closedBall (0 : Fin D → ℂ) r) := hφc.mono hsub
    have h3 : ContinuousOn ν (Metric.closedBall (0 : Fin D → ℂ) r) := hνc.mono hsub
    exact ((h1.norm.pow 2).mul ((continuousOn_const.mul h2).neg.rexp)).mul h3
  have hint : IntegrableOn (fun z => ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z)
      (Metric.ball (0 : Fin D → ℂ) r) :=
    (hcont.integrableOn_compact (isCompact_closedBall 0 r)).mono_set Metric.ball_subset_closedBall

  have hpt : ∀ z ∈ Metric.ball (0 : Fin D → ℂ) r,
      K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2)) ≤
        ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    intro z hz
    have hzρ : z ∈ Metric.ball (0 : Fin D → ℂ) ρ₀ := hsub (Metric.ball_subset_closedBall hz)
    have hzr : ‖z‖ < r := by simpa using hz
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    have hz3 : ‖z‖ ^ 3 ≤ r ^ 3 := pow_le_pow_left₀ hz0 hzr.le 3
    have hnr : (n : ℝ) * r ^ 3 = R ^ 3 / s := by
      rw [hr_def, ← hss]; field_simp
    have hφn : (n : ℝ) * φ z ≤ ∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2 + C * R ^ 3 / s := by
      have := hφ z hzρ
      have e1 : ∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2 = (n : ℝ) * ∑ j, lam j * ‖z j‖ ^ 2 := by
        rw [Finset.mul_sum]; congr 1; ext j; ring
      have e2 : C * R ^ 3 / s = C * ((n : ℝ) * r ^ 3) := by rw [hnr]; ring
      rw [e1, e2]
      have : (n : ℝ) * φ z ≤ (n : ℝ) * (∑ j, lam j * ‖z j‖ ^ 2 + C * ‖z‖ ^ 3) :=
        mul_le_mul_of_nonneg_left this hn'.le
      nlinarith [mul_le_mul_of_nonneg_left hz3 (mul_nonneg hC hn'.le)]
    have hexp : Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) * Real.exp (-(C * R ^ 3 / s)) ≤
        Real.exp (-((n : ℝ) * φ z)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hνz : 1 - C * r ≤ ν z := by
      have := hν z hzρ
      nlinarith [mul_le_mul_of_nonneg_left hzr.le hC]
    have hCr : 0 ≤ 1 - C * r := by linarith
    have hf2 : 0 ≤ ‖f z‖ ^ 2 := by positivity
    calc K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2))
        = ‖f z‖ ^ 2 * (Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) *
            Real.exp (-(C * R ^ 3 / s))) * (1 - C * r) := by rw [hK]; ring
      _ ≤ ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hf2) hνz hCr
        exact mul_nonneg hf2 (Real.exp_pos _).le
  have hmono : ∫ z in Metric.ball (0 : Fin D → ℂ) r,
      K * (‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2)) ≤
      ∫ z in Metric.ball (0 : Fin D → ℂ) r, ‖f z‖ ^ 2 * Real.exp (-((n : ℝ) * φ z)) * ν z := by
    apply integral_mono_of_nonneg _ hint
    · exact ae_restrict_of_forall_mem measurableSet_ball hpt
    · exact ae_of_all _ (fun z => mul_nonneg hK0 (mul_nonneg (by positivity) (Real.exp_pos _).le))
  rw [integral_const_mul] at hmono
  have hgauss := polydisc_gauss_le hr hRn f hf (fun j => (n : ℝ) * lam j)
  have hscale : ∀ j, discI ((n : ℝ) * lam j) r = discI (lam j) R / n := by
    intro j; rw [hr_def, hs_def]; exact discI_scale (hlam j) hR.le hn'
  have hprod : ∏ j, discI ((n : ℝ) * lam j) r = (∏ j, discI (lam j) R) / (n : ℝ) ^ D := by
    simp_rw [hscale]; rw [Finset.prod_div_distrib]; simp
  rw [hprod] at hgauss
  calc ‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D) *
        (Real.exp (-(C * R ^ 3 / s)) * (1 - C * (R / s)))
      = K * (‖f 0‖ ^ 2 * ((∏ j, discI (lam j) R) / (n : ℝ) ^ D)) := by rw [hK]; ring
    _ ≤ K * ∫ z in Metric.ball (0 : Fin D → ℂ) r,
          ‖f z‖ ^ 2 * Real.exp (-∑ j, ((n : ℝ) * lam j) * ‖z j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hgauss hK0
    _ ≤ _ := hmono
end ReciprocityTheory.GeometryOfNumbersTheory

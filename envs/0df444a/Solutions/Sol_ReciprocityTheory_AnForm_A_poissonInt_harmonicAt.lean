-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonInt_harmonicAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:52.973801+00:00
-- url     : https://prove2.me/submissions/b9de2ca2-1933-4616-864c-32974057c343

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
import Theorems.Thm_ReciprocityTheory_AnForm_A_poissonInt_eq_re
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Metric Real Filter Topology InnerProductSpace
namespace ReciprocityTheory.AnForm.A
private lemma sub_ne_zero_of_mem_sphere_of_mem_ball {r : ℝ} {w z : ℂ} (hw : w ∈ ball (0 : ℂ) r)
    (hz : z ∈ sphere (0 : ℂ) r) : z - w ≠ 0 := by
  rw [mem_ball_zero_iff] at hw
  rw [mem_sphere_zero_iff_norm] at hz
  intro h
  rw [sub_eq_zero] at h
  rw [h] at hz
  linarith
private lemma poissonInt_eq_re_cauchy_integral {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (sphere 0 r)) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w = (2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), (z - w)⁻¹ • ((g z : ℝ) : ℂ)) -
      ((Real.circleAverage g 0 r : ℝ) : ℂ)).re := by
  rw [poissonInt_eq_re hr hg hw]
  congr 1
  have hc : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
  have hAs : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ ↦ circleMap_mem_sphere 0 hr.le θ
  have hAw : ∀ θ : ℝ, circleMap 0 r θ - w ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball hw (hAs θ)
  have hgA : Continuous (fun θ : ℝ ↦ ((g (circleMap 0 r θ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hg.comp_continuous hc hAs)
  have hD : deriv (circleMap (0 : ℂ) r) = fun θ ↦ circleMap 0 r θ * I :=
    funext (deriv_circleMap 0 r)
  have hc1 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ •
      ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))) := by
    rw [hD]
    exact (hc.mul continuous_const).smul (((hc.sub continuous_const).inv₀ hAw).smul hgA)
  have hi1 : IntervalIntegrable (fun θ : ℝ ↦ -((g (circleMap 0 r θ) : ℝ) : ℂ))
      MeasureTheory.volume 0 (2 * π) := hgA.neg.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ ↦ (2 * -I) * (deriv (circleMap 0 r) θ •
      ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))))
      MeasureTheory.volume 0 (2 * π) := (continuous_const.mul hc1).intervalIntegrable _ _
  have hpt : ∀ θ : ℝ, herglotzRieszKernel 0 w (circleMap 0 r θ) • ((g (circleMap 0 r θ) : ℝ) : ℂ) =
      -((g (circleMap 0 r θ) : ℝ) : ℂ) + (2 * -I) * (deriv (circleMap 0 r) θ •
        ((circleMap 0 r θ - w)⁻¹ • ((g (circleMap 0 r θ) : ℝ) : ℂ))) := by
    intro θ
    have h1 := hAw θ
    have e : ∀ X : ℂ, (2 * -I) * (circleMap 0 r θ * I * X) = 2 * circleMap 0 r θ * X := by
      intro X
      linear_combination (-2 * circleMap 0 r θ * X) * Complex.I_mul_I
    rw [herglotzRieszKernel_def, deriv_circleMap]
    simp only [sub_zero, smul_eq_mul]
    rw [e]
    field_simp <;> ring
  unfold Real.circleAverage
  simp only [circleIntegral]
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hpt θ), intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  rw [mul_inv (2 * (π : ℂ)) I, Complex.inv_I]
  ring
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) : HarmonicAt (poissonInt g r) w := by
  have hgc : ContinuousOn (fun ζ ↦ ((g ζ : ℝ) : ℂ)) (sphere 0 r) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have hps := hasFPowerSeriesOn_cauchy_integral
    (hgc.circleIntegrable hr.le :
      CircleIntegrable (fun ζ ↦ ((g ζ : ℝ) : ℂ)) 0 ((⟨r, hr.le⟩ : NNReal) : ℝ))
    (NNReal.coe_pos.mp hr)
  have hCa : AnalyticAt ℂ
      (fun w' ↦ (2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r), (z - w')⁻¹ • ((g z : ℝ) : ℂ)) w := by
    refine hps.analyticAt_of_mem ?_
    first
    | (rw [Metric.emetric_ball_nnreal]; exact hw)
    | simpa [Metric.emetric_ball_nnreal] using hw
    | (refine EMetric.mem_ball.mpr (edist_lt_coe.mpr (NNReal.coe_lt_coe.mp ?_))
       rw [coe_nndist, dist_zero_right]
       exact mem_ball_zero_iff.mp hw)
    | (have hw' : ‖w‖ < r := mem_ball_zero_iff.mp hw
       simp only [EMetric.mem_ball, edist_zero_right, enorm_eq_nnnorm, ENNReal.coe_lt_coe]
       exact NNReal.coe_lt_coe.mp hw')
  have hFa : AnalyticAt ℂ (fun w' ↦ 2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r),
      (z - w')⁻¹ • ((g z : ℝ) : ℂ)) - ((Real.circleAverage g 0 r : ℝ) : ℂ)) w :=
    (analyticAt_const.mul hCa).sub analyticAt_const
  have hev : poissonInt g r =ᶠ[𝓝 w] fun w' ↦ (2 * ((2 * π * I : ℂ)⁻¹ • ∮ z in C(0, r),
      (z - w')⁻¹ • ((g z : ℝ) : ℂ)) - ((Real.circleAverage g 0 r : ℝ) : ℂ)).re := by
    filter_upwards [isOpen_ball.mem_nhds hw] with w' hw'
    exact poissonInt_eq_re_cauchy_integral hr hg hw'
  exact (InnerProductSpace.harmonicAt_congr_nhds hev).mpr hFa.harmonicAt_re
end ReciprocityTheory.AnForm.A

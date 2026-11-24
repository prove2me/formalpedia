-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.circleAverage_poissonKernel_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:54.15869+00:00
-- url     : https://prove2.me/submissions/393cd3d9-3a56-44fd-9ae8-ad8733419303

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshPoisson
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
private lemma re_herglotzRieszKernel_eq_poissonKernel (w z : ℂ) :
    (herglotzRieszKernel 0 w z).re = poissonKernel 0 w z := by
  rw [herglotzRieszKernel_def, poissonKernel_def]
  first
  | (simp only [sub_zero, Complex.div_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]; ring)
  | (simp only [sub_zero, Complex.div_re, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]; ring)
end ReciprocityTheory.AnForm.A
end

set_option autoImplicit false
open Complex Metric Real Filter Topology InnerProductSpace
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {r : ℝ} {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    Real.circleAverage (poissonKernel 0 w) 0 r = 1 := by
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg w) (mem_ball_zero_iff.mp hw)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) r := mem_ball_self hr
  have hD : deriv (circleMap (0 : ℂ) r) = fun θ ↦ circleMap 0 r θ * I :=
    funext (deriv_circleMap 0 r)
  have hc : Continuous (circleMap (0 : ℂ) r) := continuous_circleMap 0 r
  have hAs : ∀ θ : ℝ, circleMap 0 r θ ∈ sphere (0 : ℂ) r := fun θ ↦ circleMap_mem_sphere 0 hr.le θ
  have hAw : ∀ θ : ℝ, circleMap 0 r θ - w ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball hw (hAs θ)
  have hA0 : ∀ θ : ℝ, circleMap 0 r θ - 0 ≠ 0 := fun θ ↦ sub_ne_zero_of_mem_sphere_of_mem_ball h0 (hAs θ)
  have hc1 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) := by
    rw [hD]; exact (hc.mul continuous_const).smul ((hc.sub continuous_const).inv₀ hAw)
  have hc2 : Continuous (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹) := by
    rw [hD]; exact (hc.mul continuous_const).smul ((hc.sub continuous_const).inv₀ hA0)
  have hi1 : IntervalIntegrable
      (fun θ : ℝ ↦ (2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹))
      MeasureTheory.volume 0 (2 * π) := (continuous_const.mul hc1).intervalIntegrable _ _
  have hi2 : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)
      MeasureTheory.volume 0 (2 * π) := hc2.intervalIntegrable _ _
  have hGint : IntervalIntegrable
      (fun θ : ℝ ↦ -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) -
        deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹))
      MeasureTheory.volume 0 (2 * π) :=
    (continuous_const.mul ((continuous_const.mul hc1).sub hc2)).intervalIntegrable _ _
  have hI1 := circleIntegral.integral_sub_inv_of_mem_ball hw
  have hI2 := circleIntegral.integral_sub_inv_of_mem_ball h0
  simp only [circleIntegral] at hI1 hI2
  have hGi : ∫ θ in (0 : ℝ)..2 * π, -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹) =
      ((2 * π : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi1 hi2,
      intervalIntegral.integral_const_mul, hI1, hI2]
    push_cast
    linear_combination (-2 * (π : ℂ)) * Complex.I_mul_I
  have hpt : ∀ θ : ℝ, poissonKernel 0 w (circleMap 0 r θ) =
      (-I * ((2 : ℂ) * (deriv (circleMap 0 r) θ • (circleMap 0 r θ - w)⁻¹) -
        deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re := by
    intro θ
    rw [← re_herglotzRieszKernel_eq_poissonKernel, herglotzRieszKernel_def, deriv_circleMap]
    congr 1
    have h1 := hAw θ
    have h2 := hA0 θ
    simp only [sub_zero, smul_eq_mul] at h2 ⊢
    have hII : -I * I = 1 := by rw [neg_mul, Complex.I_mul_I, neg_neg]
    calc (circleMap 0 r θ + w) / (circleMap 0 r θ - w)
        = circleMap 0 r θ * (2 * (circleMap 0 r θ - w)⁻¹ - (circleMap 0 r θ)⁻¹) := by
          field_simp <;> ring
      _ = (-I * I) * (circleMap 0 r θ * (2 * (circleMap 0 r θ - w)⁻¹ - (circleMap 0 r θ)⁻¹)) := by
          rw [hII, one_mul]
      _ = -I * (2 * (circleMap 0 r θ * I * (circleMap 0 r θ - w)⁻¹) -
            circleMap 0 r θ * I * (circleMap 0 r θ)⁻¹) := by ring
  have hre : ∫ θ in (0 : ℝ)..2 * π, (-I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re =
      (∫ θ in (0 : ℝ)..2 * π, -I * ((2 : ℂ) * (deriv (circleMap 0 r) θ •
      (circleMap 0 r θ - w)⁻¹) - deriv (circleMap 0 r) θ • (circleMap 0 r θ - 0)⁻¹)).re := by
    first
    | exact Complex.reCLM.intervalIntegral_comp_comm hGint
    | exact intervalIntegral.integral_re hGint
  unfold Real.circleAverage
  rw [intervalIntegral.integral_congr (fun θ _ ↦ hpt θ), hre, hGi, Complex.ofReal_re, smul_eq_mul]
  exact inv_mul_cancel₀ (by positivity)
end ReciprocityTheory.AnForm.A

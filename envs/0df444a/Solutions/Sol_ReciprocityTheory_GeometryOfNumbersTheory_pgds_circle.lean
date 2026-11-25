-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.pgds_circle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:02:08.752055+00:00
-- url     : https://prove2.me/submissions/7282127c-f41b-4710-be83-bb128e35ca92

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_DiscSt

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
theorem _root_.solution {R s : ℝ} (hs : 0 < s) (hsR : s < R) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball 0 R)) :
    2 * Real.pi * ‖g 0‖ ^ 2 ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, ‖g (Complex.polarCoord.symm (s, θ))‖ ^ 2 := by
  have hpi := Real.pi_pos
  set h : ℂ → ℂ := fun z => g z ^ 2 with hh
  have habs : |s| = s := abs_of_pos hs
  have hdiff : DiffContOnCl ℂ h (Metric.ball 0 |s|) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (by rw [habs]; exact hs.ne'), habs]
    exact (hg.pow 2).mono (Metric.closedBall_subset_ball hsR)
  have hav := hdiff.circleAverage
  rw [Real.circleAverage_def] at hav
  have hper : Function.Periodic (fun θ => ‖h (circleMap 0 s θ)‖) (2 * Real.pi) := by
    intro θ; simp only; rw [periodic_circleMap 0 s θ]
  have e1 := hper.intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at e1
  have hle : ‖h 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2 * Real.pi, ‖h (circleMap 0 s θ)‖ := by
    rw [← hav, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    gcongr
    exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
  rw [e1, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo] at hle
  have hcm : ∀ θ : ℝ, circleMap 0 s θ = Complex.polarCoord.symm (s, θ) := by
    intro θ
    simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I]
  simp only [hcm, hh, norm_pow] at hle
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)] at hle
  linarith
end ReciprocityTheory.GeometryOfNumbersTheory

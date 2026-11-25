-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.poissonInt_eq_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:06:54.840961+00:00
-- url     : https://prove2.me/submissions/5a102ded-5fa3-44a5-8b20-19e9824bbce3

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
theorem _root_.solution {g : ℂ → ℝ} {r : ℝ} (hr : 0 < r) (hg : ContinuousOn g (sphere 0 r))
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    poissonInt g r w =
      (Real.circleAverage (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r).re := by
  have hH : ContinuousOn (herglotzRieszKernel 0 w) (sphere 0 r) := by
    rw [show herglotzRieszKernel 0 w = fun ζ ↦ (ζ - 0 + (w - 0)) / (ζ - 0 - (w - 0)) from
      funext (herglotzRieszKernel_def 0 w)]
    refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) ?_
    intro z hz
    simpa using sub_ne_zero_of_mem_sphere_of_mem_ball hw hz
  have hgc : ContinuousOn (fun ζ ↦ (g ζ : ℂ)) (sphere 0 r) :=
    Complex.continuous_ofReal.comp_continuousOn hg
  have hi : CircleIntegrable (fun ζ ↦ herglotzRieszKernel 0 w ζ • (g ζ : ℂ)) 0 r :=
    (hH.smul hgc).circleIntegrable hr.le
  have hre : ∫ θ in (0 : ℝ)..2 * π,
      (herglotzRieszKernel 0 w (circleMap 0 r θ) • (g (circleMap 0 r θ) : ℂ)).re =
      (∫ θ in (0 : ℝ)..2 * π,
        herglotzRieszKernel 0 w (circleMap 0 r θ) • (g (circleMap 0 r θ) : ℂ)).re := by
    first
    | exact Complex.reCLM.intervalIntegral_comp_comm hi
    | exact intervalIntegral.integral_re hi
  unfold poissonInt Real.circleAverage
  rw [Complex.smul_re, ← hre]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, re_herglotzRieszKernel_eq_poissonKernel]
end ReciprocityTheory.AnForm.A

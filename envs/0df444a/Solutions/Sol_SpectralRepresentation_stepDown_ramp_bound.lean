-- Prove2me | solution 1 for SpectralRepresentation.stepDown_ramp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:03:30.938339+00:00
-- url     : https://prove2.me/submissions/037e28a1-7d74-4a7c-9238-a474aab59088

module
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Definitions.Def_BasicResults_Spectral_MonotoneConvergence
public import Definitions.Def_BasicResults_Spectral_Projection
public import Theorems.Thm_SpectralRepresentation_stepDown_nonneg
public import Theorems.Thm_SpectralRepresentation_stepDown_eq_one

set_option autoImplicit true
@[expose] public section
public section
open ContinuousLinearMap
open SpectralRepresentation
namespace SpectralRepresentation
theorem _root_.solution (t : ℝ) (n : ℕ) (s : ℝ) :
    |(s - t) * stepDown t n s - max (s - t) 0| ≤ ((n : ℝ) + 1)⁻¹ := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rcases le_total t s with hts | hst
  · rw [stepDown_eq_one t n hts, max_eq_left (by linarith : (0 : ℝ) ≤ s - t), mul_one,
      sub_self, abs_zero]
    positivity
  · rw [max_eq_right (by linarith : s - t ≤ (0 : ℝ)), sub_zero,
      abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (by linarith) (stepDown_nonneg t n s)),
      show -((s - t) * stepDown t n s) = (t - s) * stepDown t n s by ring]
    refine (mul_le_mul_of_nonneg_left
      (max_le_max le_rfl (min_le_right (1 : ℝ) _) : stepDown t n s ≤ max 0 (1 + ((n : ℝ) + 1) * (s - t)))
      (by linarith : (0 : ℝ) ≤ t - s)).trans ?_
    rcases le_total (1 + ((n : ℝ) + 1) * (s - t)) 0 with h | h
    · rw [max_eq_left h, mul_zero]; positivity
    · rw [max_eq_right h, inv_eq_one_div, le_div_iff₀ hn1]
      nlinarith [sq_nonneg (((n : ℝ) + 1) * (t - s) - 1 / 2)]
end SpectralRepresentation

-- Prove2me | solution 1 for Sendov.norm_mul_norm_inv_sub_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:01:55.803614+00:00
-- url     : https://prove2.me/submissions/f4e64c27-891a-4e84-8877-fcfb78ca29e3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Sendov_Analytic_Defect

set_option autoImplicit false
open Sendov
open Multiset
namespace Sendov
theorem _root_.solution {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ ≤ 1 - ‖w‖ ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hne
  · simp
  · have hkey : w * (w⁻¹ - (starRingEnd ℂ) w) = 1 - ((‖w‖ : ℝ) : ℂ) ^ 2 := by
      rw [mul_sub, mul_inv_cancel₀ hne, Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
    have h1 : ‖w‖ * ‖w⁻¹ - (starRingEnd ℂ) w‖ = ‖(1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2‖ := by
      rw [← norm_mul, hkey]
    rw [h1]
    have h2 : ((1 : ℂ) - ((‖w‖ : ℝ) : ℂ) ^ 2) = ((1 - ‖w‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith [norm_nonneg w])]
end Sendov

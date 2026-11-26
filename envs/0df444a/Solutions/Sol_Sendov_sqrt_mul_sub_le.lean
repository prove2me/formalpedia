-- Prove2me | solution 1 for Sendov.sqrt_mul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:03.862033+00:00
-- url     : https://prove2.me/submissions/24e016cb-5208-40b7-9cb8-8966c7ba047d

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.MeanValue
import Definitions.Def_Sendov_Common_Sinh
import Theorems.Thm_Sendov_sinh_sq_le
section
namespace Sendov
open Real Set Filter
private lemma nonneg_of_deriv {f g : ℝ → ℝ} (hd : ∀ z, HasDerivAt f (g z) z)
    (h0 : f 0 = 0) (hg : ∀ z, 0 ≤ z → 0 ≤ g z) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ f y := by
  have hmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun z _ => (hd z).continuousAt.continuousWithinAt)
      (fun z hz => (hd z).differentiableAt.differentiableWithinAt) (fun z hz => ?_)
    rw [(hd z).deriv]
    rw [interior_Ici] at hz
    exact hg z (le_of_lt hz)
  simpa [h0] using hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hy) hy
private lemma sinh_le_mul_cosh {h : ℝ} (hh : 0 ≤ h) : sinh h ≤ h * cosh h := by
  have : 0 ≤ h * cosh h - sinh h := by
    refine nonneg_of_deriv (f := fun t => t * cosh t - sinh t) (g := fun t => t * sinh t)
      (fun t => ?_) (by simp) (fun t ht => mul_nonneg ht (sinh_nonneg_iff.2 ht)) hh
    exact (((hasDerivAt_id' t).mul (hasDerivAt_cosh t)).sub (hasDerivAt_sinh t)).congr_deriv
      (by ring)
  linarith
end Sendov
end

set_option autoImplicit false
open Sendov
open Real Set Filter
namespace Sendov
theorem _root_.solution {h : ℝ} (hh : 0 ≤ h) :
    sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) ≤ h ^ 2 * sinh h := by
  have : (0 : ℝ) ≤ h ^ 2 * sinh h := mul_nonneg (sq_nonneg h) (sinh_nonneg_iff.2 hh)
  have : (0 : ℝ) ≤ sqrt (h ^ 2 + 9) * (h * cosh h - sinh h) :=
    mul_nonneg (sqrt_nonneg _) (by linarith [sinh_le_mul_cosh hh])
  have : (sqrt (h ^ 2 + 9) * (h * cosh h - sinh h)) ^ 2 ≤ (h ^ 2 * sinh h) ^ 2 := by
    convert sinh_sq_le hh
    · rw [mul_pow, sq_sqrt (by positivity)]
    ·  ring
  nlinarith
end Sendov

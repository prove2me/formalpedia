-- Prove2me | solution 1 for QuantumLinSys.Fourier.bound_p13
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T02:01:45.071502+00:00
-- url     : https://prove2.me/submissions/b6aec0d1-d590-4640-ac47-dc0c56556758

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/- The denominator is at least 5|x|/6, whereas the second-order
   exponential remainder is at most 3|x|²/4. -/
theorem solution (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    ‖1 / (1 - Complex.exp (-Complex.I * x)) -
      1 / (Complex.I * x)‖ < 1 := by
  have ha : |x| ≤ 1 := abs_le.mpr hx
  have hp : 0 < |x| := abs_pos.mpr hx0
  have hc : |x| ^ 3 ≤ |x| := by
    calc
      |x| ^ 3 ≤ |x| ^ 1 := pow_le_pow_of_le_one (abs_nonneg x) ha (by norm_num)
      _ = |x| := pow_one _
  have hs : (5 / 6 : ℝ) * |x| ≤ |Real.sin x| := by
    have h₁ := Real.abs_sub_sin_le x
    have h₂ := abs_sub_abs_le_abs_sub x (Real.sin x)
    linarith
  have hd : (5 / 6 : ℝ) * |x| ≤ ‖1 - Complex.exp (-Complex.I * x)‖ := by
    apply hs.trans
    simpa [Complex.exp_im] using
      Complex.abs_im_le_norm (1 - Complex.exp (-Complex.I * x))
  have hdpos : 0 < ‖1 - Complex.exp (-Complex.I * x)‖ :=
    lt_of_lt_of_le (by positivity) hd
  have hdn : 1 - Complex.exp (-Complex.I * x) ≠ 0 := norm_pos_iff.mp hdpos
  have hxn : Complex.I * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx0)
  have hr : ‖Complex.exp (-Complex.I * x) - 1 - (-Complex.I * x)‖ ≤
      |x| ^ 2 * (3 / 4 : ℝ) := by
    have hb := Complex.exp_bound (x := -Complex.I * x) (by simpa using ha)
      (n := 2) (by norm_num)
    convert hb using 1 <;> norm_num [Finset.sum_range_succ, Nat.factorial]
    congr 1
    ring
  have heq : 1 / (1 - Complex.exp (-Complex.I * x)) - 1 / (Complex.I * x) =
      (Complex.exp (-Complex.I * x) - 1 - (-Complex.I * x)) /
        ((1 - Complex.exp (-Complex.I * x)) * (Complex.I * x)) := by
    rw [div_sub_div _ _ hdn hxn]
    congr 1
    ring
  rw [heq, norm_div, norm_mul]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
  apply (div_lt_one (mul_pos hdpos hp)).mpr
  apply lt_of_le_of_lt hr
  have hm := mul_le_mul_of_nonneg_right hd hp.le
  nlinarith [sq_pos_of_pos hp]

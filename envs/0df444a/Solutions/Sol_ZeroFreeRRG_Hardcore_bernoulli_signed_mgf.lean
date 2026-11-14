-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.bernoulli_signed_mgf
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:38:50.524424+00:00
-- url     : https://prove2.me/submissions/da3244af-fd8f-481c-b0ab-10c55b6a46d2

import Mathlib
set_option autoImplicit false

private theorem exp_sharp (x : ℝ) (hx : |x| ≤ 1/3) : Real.exp x ≤ 1+x+(3/4)*x^2 := by
  have hx1 : |x| ≤ 1 := by linarith
  have hh := Real.exp_bound (n := 3) hx1 (by norm_num)
  norm_num [Finset.sum_range_succ] at hh
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hx2 : 0 ≤ x^2 := sq_nonneg x
  have h3 : |x|^3 ≤ (1/3)*x^2 := by
    have hsq : |x|^2 = x^2 := sq_abs x
    have hh := mul_le_mul_of_nonneg_right hx hx2
    nlinarith [sq_abs x, sq_nonneg (|x|)]
  have he := le_abs_self (Real.exp x - (1 + x + x^2/2))
  nlinarith

theorem solution (s θ z : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1/3) (hz : |z| ≤ 1) :
    (1-s+s*Real.exp (θ*z))*Real.exp (-(s*θ*z)) ≤ Real.exp ((3/4)*s*θ^2) := by
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hsq : z^2 ≤ 1 := by nlinarith [sq_abs z, sq_nonneg (|z|)]
  have hθz : |θ*z| ≤ 1/3 := by rw [abs_mul,abs_of_nonneg hθ]; nlinarith
  have he := exp_sharp (θ*z) hθz
  have hu : (θ*z)^2 ≤ θ^2 := by nlinarith [sq_nonneg θ, mul_nonneg (sq_nonneg θ) (sub_nonneg.mpr hsq)]
  have hh : 1-s+s*Real.exp (θ*z) ≤ 1+(s*θ*z)+(3/4)*s*θ^2 := by
    have hm := mul_le_mul_of_nonneg_left he hs
    have hu' := mul_le_mul_of_nonneg_left hu hs
    nlinarith
  have he' := Real.add_one_le_exp ((s*θ*z)+(3/4)*s*θ^2)
  have hbound : 1-s+s*Real.exp (θ*z) ≤ Real.exp ((s*θ*z)+(3/4)*s*θ^2) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-(s*θ*z))).le
  rw [← Real.exp_add] at hmul
  have heq : (s*θ*z)+(3/4)*s*θ^2 + -(s*θ*z) = (3/4)*s*θ^2 := by ring
  simpa only [heq] using hmul

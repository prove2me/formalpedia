-- Prove2me | solution 1 for Roberts1997.RWM.min_one_exp_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:26.621342+00:00
-- url     : https://prove2.me/submissions/4ca54024-7d8f-4567-8b41-f207c6162443

import Mathlib

/-- On `(-∞, 0]` the exponential is `1`-Lipschitz, in the sharp additive form. -/
private theorem expkey (u v : ℝ) (huv : u ≤ v) (hv : v ≤ 0) :
    Real.exp v - Real.exp u ≤ v - u := by
  have hev : 0 < Real.exp v := Real.exp_pos v
  have hle : Real.exp v ≤ 1 := by simpa using Real.exp_le_exp.mpr hv
  have h1 : (u - v) + 1 ≤ Real.exp (u - v) := Real.add_one_le_exp (u - v)
  have h3 : Real.exp v * ((u - v) + 1) ≤ Real.exp u := by
    calc Real.exp v * ((u - v) + 1) ≤ Real.exp v * Real.exp (u - v) :=
          mul_le_mul_of_nonneg_left h1 hev.le
      _ = Real.exp u := by rw [← Real.exp_add]; congr 1; ring
  nlinarith [h3, hle, sub_nonneg.mpr huv]

private theorem minexp (x : ℝ) : min 1 (Real.exp x) = Real.exp (min 0 x) := by
  rcases le_total 0 x with h | h
  · have h1 : (1 : ℝ) ≤ Real.exp x := by simpa using Real.exp_le_exp.mpr h
    rw [min_eq_left h, Real.exp_zero, min_eq_left h1]
  · have h1 : Real.exp x ≤ 1 := by simpa using Real.exp_le_exp.mpr h
    rw [min_eq_right h, min_eq_right h1]

private theorem minlip (x y : ℝ) : |min 0 x - min 0 y| ≤ |x - y| := by
  have h1 := le_abs_self (x - y)
  have h2 := neg_abs_le (x - y)
  have h0 := abs_nonneg (x - y)
  rw [abs_le]
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · rw [min_eq_left hx, min_eq_left hy]; constructor <;> linarith
  · rw [min_eq_left hx, min_eq_right hy]; constructor <;> linarith
  · rw [min_eq_right hx, min_eq_left hy]; constructor <;> linarith
  · rw [min_eq_right hx, min_eq_right hy]; constructor <;> linarith

theorem solution (x y : ℝ) :
    |min 1 (Real.exp x) - min 1 (Real.exp y)| ≤ |x - y| := by
  rw [minexp x, minexp y]
  refine le_trans ?_ (minlip x y)
  rcases le_total (min 0 x) (min 0 y) with h | h
  · rw [abs_sub_comm (Real.exp (min 0 x)), abs_sub_comm (min 0 x),
      abs_of_nonneg (by linarith [Real.exp_le_exp.mpr h] :
        (0 : ℝ) ≤ Real.exp (min 0 y) - Real.exp (min 0 x)),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ min 0 y - min 0 x)]
    exact expkey (min 0 x) (min 0 y) h (min_le_left _ _)
  · rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr h] :
        (0 : ℝ) ≤ Real.exp (min 0 x) - Real.exp (min 0 y)),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ min 0 x - min 0 y)]
    exact expkey (min 0 y) (min 0 x) h (min_le_left _ _)

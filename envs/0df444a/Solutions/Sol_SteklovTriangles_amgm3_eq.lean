-- Prove2me | solution 1 for SteklovTriangles.amgm3_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:50:49.732407+00:00
-- url     : https://prove2.me/submissions/f4548c25-5e9e-4ed7-b57d-9bfa14119544

import Mathlib
import Definitions.Def_SteklovTriangles_AreaCorollary

set_option autoImplicit false
open SteklovTriangles
namespace SteklovTriangles
theorem _root_.solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : 27 * (x * y * z) = (x + y + z) ^ 3) : x = y ∧ y = z := by
  -- (x+y+z)^3 - 27xyz ≥ (x+y+z) * ((x-y)^2+(y-z)^2+(z-x)^2) / 2 ≥ 0
  have hsum : 0 ≤ x + y + z := by linarith
  have key : (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) ≤ 2 * ((x + y + z) ^ 3 - 27 * (x * y * z)) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z),
      mul_nonneg hz (sq_nonneg (x - y)), mul_nonneg hx (sq_nonneg (y - z)),
      mul_nonneg hy (sq_nonneg (x - z)), mul_nonneg (mul_nonneg hx hy) hz,
      sq_nonneg (x + y - 2 * z), sq_nonneg (x - 2 * y + z), sq_nonneg (-2 * x + y + z)]
  rw [h, sub_self, mul_zero] at key
  rcases eq_or_lt_of_le hsum with h0 | hpos
  · constructor <;> linarith
  · have hq : (x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2 ≤ 0 := by
      by_contra hcon
      have := mul_pos hpos (lt_of_not_ge hcon)
      linarith
    have e1 : (x - y) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have e2 : (y - z) ^ 2 = 0 := by nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    constructor
    · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp e1]
    · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp e2]
end SteklovTriangles

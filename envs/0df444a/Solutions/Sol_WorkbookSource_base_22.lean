-- Prove2me | solution 1 for WorkbookSource.base_22
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:36:13.408872+00:00
-- url     : https://prove2.me/submissions/c0f5f6f7-3739-449d-b935-665908b444ad

import Mathlib
set_option autoImplicit false
theorem solution (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (habc : a + b + c + d = 4) : 1 / (a + b) / (c + d) + 1 / (b + c) / (d + a) + 1 / (c + a) / (b + d) ≥ 3 / 4  := by
  have key (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 4) :
      (1 : ℝ) / 4 ≤ 1 / x / y := by
    have hp : 0 < x * y := mul_pos hx hy
    have hprod : x * y ≤ 4 := by nlinarith [sq_nonneg (x-y)]
    have hi := one_div_le_one_div_of_le hp hprod
    simpa [div_eq_mul_inv, mul_comm] using hi
  have h1 := key (a+b) (c+d) (by positivity) (by positivity) (by linarith)
  have h2 := key (b+c) (d+a) (by positivity) (by positivity) (by linarith)
  have h3 := key (c+a) (b+d) (by positivity) (by positivity) (by linarith)
  linarith
#print axioms solution

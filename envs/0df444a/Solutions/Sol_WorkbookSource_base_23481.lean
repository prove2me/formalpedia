-- Prove2me | solution 1 for WorkbookSource.base_23481
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:59:48.628555+00:00
-- url     : https://prove2.me/submissions/23f81658-277a-4788-a8ed-7eeae75a0b67

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * x ^ 2 + 2 * x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 1 / 3  := by
  have hn : 0 ≤ (9*x^2 + 6*x*y^2 + 3*x*y*z^2 - 12*x*y*z + 1) := by
    have hs0 : 0 ≤ (9 : ℝ) * (1) * (x - 1/3)^2 := by positivity
    have hs1 : 0 ≤ (6 : ℝ) * (x) * (1 - y)^2 := by positivity
    have hs2 : 0 ≤ (12 : ℝ) * (x*y) * (1 - z/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hd : (0 : ℝ) < (3) := by positivity
  have heqrat : ( 3 * x ^ 2 + 2 * x * y ^ 2 + x * y * z ^ 2 ) - ( 4 * x * y * z - 1 / 3  ) = (9*x^2 + 6*x*y^2 + 3*x*y*z^2 - 12*x*y*z + 1) / (3) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 3 * x ^ 2 + 2 * x * y ^ 2 + x * y * z ^ 2 ≥ 4 * x * y * z - 1 / 3) := @solution
#print axioms solution

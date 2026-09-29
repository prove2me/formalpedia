-- Prove2me | solution 1 for WorkbookSource.base_5609
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:35.798251+00:00
-- url     : https://prove2.me/submissions/e857b25f-75d9-4aeb-8e62-11dfa6b6b55c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :  3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 24 * x * y * z / (x * y * z + (x + y) * (y + z) * (z + x)) + 4 * (x * y + y * z + z * x) / (x + y + z) ^ 2 ≥ 7  := by
  have hn : 0 ≤ (3*x^4 - x^3*y - x^3*z - 4*x^2*y^2 + 3*x^2*y*z - 4*x^2*z^2 - x*y^3 + 3*x*y^2*z + 3*x*y*z^2 - x*z^3 + 3*y^4 - y^3*z - 4*y^2*z^2 - y*z^3 + 3*z^4) := by
    have hs0 : 0 ≤ (3 : ℝ) * (1) * (-x^2/2 + x*y - x*z/2 - y^2/2 - y*z/2 + z^2)^2 := by positivity
    have hs1 : 0 ≤ (9/4 : ℝ) * (1) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
    have hs2 : 0 ≤ (2 : ℝ) * (y*z) * (-y + z)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (x*z) * (-x + z)^2 := by positivity
    have hs4 : 0 ≤ (2 : ℝ) * (x*y) * (-x + y)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : 0 < ((x + y + z)^2*(x*y + x*z + y*z)) := by positivity
  have he : (  3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 24 * x * y * z / (x * y * z + (x + y) * (y + z) * (z + x)) + 4 * (x * y + y * z + z * x) / (x + y + z) ^ 2 ) - ( 7  ) = (3*x^4 - x^3*y - x^3*z - 4*x^2*y^2 + 3*x^2*y*z - 4*x^2*z^2 - x*y^3 + 3*x*y^2*z + 3*x*y*z^2 - x*z^3 + 3*y^4 - y^3*z - 4*y^2*z^2 - y*z^3 + 3*z^4) / ((x + y + z)^2*(x*y + x*z + y*z)) := by
    field_simp
    <;> ring
  have hzpos := div_nonneg hn (le_of_lt hd)
  linarith only [he, hzpos]

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 24 * x * y * z / (x * y * z + (x + y) * (y + z) * (z + x)) + 4 * (x * y + y * z + z * x) / (x + y + z) ^ 2 ≥ 7) := @solution
#print axioms solution

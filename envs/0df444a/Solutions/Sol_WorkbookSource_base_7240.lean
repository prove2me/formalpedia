-- Prove2me | solution 1 for WorkbookSource.base_7240
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:45:54.657014+00:00
-- url     : https://prove2.me/submissions/5c842592-0930-47c7-98a2-33c7e26e793f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z = 3) : y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 ≥ 3 * x * y * z  := by
  have helim : z = (-x - y + 3) := by linarith only [h]
  have hsum : 0 ≤ (9 : ℝ) * (x^2/6 - x*y/3 - x/2 - y^2/3 + y)^2 + (27/4 : ℝ) * (-x^2/3 - 2*x*y/3 + x)^2 := by positivity
  have hid : ( y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 ) - ( 3 * x * y * z  ) = (9 : ℝ) * (x^2/6 - x*y/3 - x/2 - y^2/3 + y)^2 + (27/4 : ℝ) * (-x^2/3 - 2*x*y/3 + x)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z = 3), y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 ≥ 3 * x * y * z) := @solution
#print axioms solution

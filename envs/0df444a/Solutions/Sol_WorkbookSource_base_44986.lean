-- Prove2me | solution 1 for WorkbookSource.base_44986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:32.286718+00:00
-- url     : https://prove2.me/submissions/6c4295b7-3038-4403-87b9-199df6b0159d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
  x ^ 3 * y + y ^ 3 * z + z ^ 3 * x ≤ 3  := by
  have hw0 : 0 ≤ (x^2 + y^2 + z^2 - 3) := by linarith only [h]
  have hw1 : 0 ≤ (-x^2 - y^2 - z^2 + 3) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (x^2/2 - x*y/2 - x*z/2 - y^2/2 + y*z)^2 + (3/4 : ℝ) * (1) * (x^2/3 - x*y + x*z + y^2/3 - 2*z^2/3)^2 + (1 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (z)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (y)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (x)^2 := by positivity
  have hid : ( 3  ) - (
  x ^ 3 * y + y ^ 3 * z + z ^ 3 * x ) = (1 : ℝ) * (1) * (x^2/2 - x*y/2 - x*z/2 - y^2/2 + y*z)^2 + (3/4 : ℝ) * (1) * (x^2/3 - x*y + x*z + y^2/3 - 2*z^2/3)^2 + (1 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (z)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (y)^2 + (1/3 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (x)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 3), x ^ 3 * y + y ^ 3 * z + z ^ 3 * x ≤ 3) := @solution
#print axioms solution

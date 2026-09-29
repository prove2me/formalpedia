-- Prove2me | solution 1 for WorkbookSource.plus_31230
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:56.075934+00:00
-- url     : https://prove2.me/submissions/72e57f2d-f858-443b-b897-c6836e683bc5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) : (3 * (y - z) ^ 2 * x ^ 6 + 9 * (y + z) * (y - z) ^ 2 * x ^ 5 + (12 * z ^ 4 - 9 * y * z ^ 3 - 2 * y ^ 2 * z ^ 2 + 12 * y ^ 4 - 9 * y ^ 3 * z) * x ^ 4 + (y + z) * (3 * z ^ 2 - 4 * y * z + 3 * y ^ 2) * (3 * z ^ 2 - 2 * y * z + 3 * y ^ 2) * x ^ 3 + (-9 * z * y ^ 5 + 3 * y ^ 6 - 2 * y ^ 2 * z ^ 4 - 2 * y ^ 4 * z ^ 2 + 3 * z ^ 6 - 9 * y * z ^ 5 + 8 * y ^ 3 * z ^ 3) * x ^ 2 - 3 * y * z * (y + z) * (2 * z ^ 4 + y * z ^ 3 + 2 * y ^ 2 * z ^ 2 + y ^ 3 * z + 2 * y ^ 4) * x + 3 * y ^ 2 * z ^ 2 * (y ^ 2 + y * z + z ^ 2) * (y + z) ^ 2) ≥ 0   := by
  have hsum : 0 ≤ (9 : ℝ) * (-x^2*y^2/2 + x^2*y*z/3 - x^2*z^2/2 - x*y^3/2 - x*y^2*z/6 - x*y*z^2/6 - x*z^3/2 + y^3*z/2 + y^2*z^2 + y*z^3/2)^2 + (27/4 : ℝ) * (-2*x^3*y/3 + 2*x^3*z/3 - x^2*y^2 + x^2*z^2 - x*y^3/3 + x*y^2*z/3 - x*y*z^2/3 + x*z^3/3 + y^3*z/3 - y*z^3/3)^2 := by positivity
  have hid : ( (3 * (y - z) ^ 2 * x ^ 6 + 9 * (y + z) * (y - z) ^ 2 * x ^ 5 + (12 * z ^ 4 - 9 * y * z ^ 3 - 2 * y ^ 2 * z ^ 2 + 12 * y ^ 4 - 9 * y ^ 3 * z) * x ^ 4 + (y + z) * (3 * z ^ 2 - 4 * y * z + 3 * y ^ 2) * (3 * z ^ 2 - 2 * y * z + 3 * y ^ 2) * x ^ 3 + (-9 * z * y ^ 5 + 3 * y ^ 6 - 2 * y ^ 2 * z ^ 4 - 2 * y ^ 4 * z ^ 2 + 3 * z ^ 6 - 9 * y * z ^ 5 + 8 * y ^ 3 * z ^ 3) * x ^ 2 - 3 * y * z * (y + z) * (2 * z ^ 4 + y * z ^ 3 + 2 * y ^ 2 * z ^ 2 + y ^ 3 * z + 2 * y ^ 4) * x + 3 * y ^ 2 * z ^ 2 * (y ^ 2 + y * z + z ^ 2) * (y + z) ^ 2) ) - ( 0   ) = (9 : ℝ) * (-x^2*y^2/2 + x^2*y*z/3 - x^2*z^2/2 - x*y^3/2 - x*y^2*z/6 - x*y*z^2/6 - x*z^3/2 + y^3*z/2 + y^2*z^2 + y*z^3/2)^2 + (27/4 : ℝ) * (-2*x^3*y/3 + 2*x^3*z/3 - x^2*y^2 + x^2*z^2 - x*y^3/3 + x*y^2*z/3 - x*y*z^2/3 + x*z^3/3 + y^3*z/3 - y*z^3/3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ), (3 * (y - z) ^ 2 * x ^ 6 + 9 * (y + z) * (y - z) ^ 2 * x ^ 5 + (12 * z ^ 4 - 9 * y * z ^ 3 - 2 * y ^ 2 * z ^ 2 + 12 * y ^ 4 - 9 * y ^ 3 * z) * x ^ 4 + (y + z) * (3 * z ^ 2 - 4 * y * z + 3 * y ^ 2) * (3 * z ^ 2 - 2 * y * z + 3 * y ^ 2) * x ^ 3 + (-9 * z * y ^ 5 + 3 * y ^ 6 - 2 * y ^ 2 * z ^ 4 - 2 * y ^ 4 * z ^ 2 + 3 * z ^ 6 - 9 * y * z ^ 5 + 8 * y ^ 3 * z ^ 3) * x ^ 2 - 3 * y * z * (y + z) * (2 * z ^ 4 + y * z ^ 3 + 2 * y ^ 2 * z ^ 2 + y ^ 3 * z + 2 * y ^ 4) * x + 3 * y ^ 2 * z ^ 2 * (y ^ 2 + y * z + z ^ 2) * (y + z) ^ 2) ≥ 0) := @solution
#print axioms solution

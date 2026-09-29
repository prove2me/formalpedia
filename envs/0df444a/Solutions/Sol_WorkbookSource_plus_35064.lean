-- Prove2me | solution 1 for WorkbookSource.plus_35064
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:34.568865+00:00
-- url     : https://prove2.me/submissions/8232a3e2-533b-4e6d-adb5-ba1d61ff0645

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x ^ 4 - 8 * x ^ 3 * y + 18 * x ^ 2 * y ^ 2 + x * y ^ 3 - 12 * x * y * z ^ 2) + (y ^ 4 - 8 * y ^ 3 * z + 18 * y ^ 2 * z ^ 2 + y * z ^ 3 - 12 * y * z * x ^ 2) + (z ^ 4 - 8 * z ^ 3 * x + 18 * z ^ 2 * x ^ 2 + z * x ^ 3 - 12 * z * x * y ^ 2) ≥ 0   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x + y + z - 3) := by linarith only [h]
  have hw4 : 0 ≤ (-x - y - z + 3) := by linarith only [h]
  have hsum : 0 ≤ (19 : ℝ) * (1) * (7*x^2/38 - x*y/2 - x*z/2 - 4*y^2/19 + y*z + z^2/38)^2 + (57/4 : ℝ) * (1) * (3*x^2/19 - x*y + x*z + 2*y^2/19 - 5*z^2/19)^2 := by positivity
  have hid : ( (x ^ 4 - 8 * x ^ 3 * y + 18 * x ^ 2 * y ^ 2 + x * y ^ 3 - 12 * x * y * z ^ 2) + (y ^ 4 - 8 * y ^ 3 * z + 18 * y ^ 2 * z ^ 2 + y * z ^ 3 - 12 * y * z * x ^ 2) + (z ^ 4 - 8 * z ^ 3 * x + 18 * z ^ 2 * x ^ 2 + z * x ^ 3 - 12 * z * x * y ^ 2) ) - ( 0   ) = (19 : ℝ) * (1) * (7*x^2/38 - x*y/2 - x*z/2 - 4*y^2/19 + y*z + z^2/38)^2 + (57/4 : ℝ) * (1) * (3*x^2/19 - x*y + x*z + 2*y^2/19 - 5*z^2/19)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), (x ^ 4 - 8 * x ^ 3 * y + 18 * x ^ 2 * y ^ 2 + x * y ^ 3 - 12 * x * y * z ^ 2) + (y ^ 4 - 8 * y ^ 3 * z + 18 * y ^ 2 * z ^ 2 + y * z ^ 3 - 12 * y * z * x ^ 2) + (z ^ 4 - 8 * z ^ 3 * x + 18 * z ^ 2 * x ^ 2 + z * x ^ 3 - 12 * z * x * y ^ 2) ≥ 0) := @solution
#print axioms solution

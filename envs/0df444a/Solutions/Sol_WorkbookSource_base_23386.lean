-- Prove2me | solution 1 for WorkbookSource.base_23386
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:41.225855+00:00
-- url     : https://prove2.me/submissions/51fbee0d-347d-46ef-8d8b-4d2d74847ee5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : (z * x + y ^ 2) * (x * y + z ^ 2) * (y * z + x ^ 2) ≥ (z * x + z ^ 2) * (x * y + x ^ 2) * (y * z + y ^ 2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (y*z) * (-x^2/3 - x*y/3 - x*z/3 + y*z)^2 := by positivity
  have h1 : 0 ≤ (8/9 : ℝ) * (y*z) * (x^2 - x*y/2 - x*z/2)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (x*z) * (-x*y/3 - x*z/3 + y^2 - y*z/3)^2 := by positivity
  have h3 : 0 ≤ (8/9 : ℝ) * (x*z) * (-x*y/2 + x*z - y*z/2)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (x*y) * (-x*y/3 - x*z/3 - y*z/3 + z^2)^2 := by positivity
  have h5 : 0 ≤ (8/9 : ℝ) * (x*y) * (x*y - x*z/2 - y*z/2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0), (z * x + y ^ 2) * (x * y + z ^ 2) * (y * z + x ^ 2) ≥ (z * x + z ^ 2) * (x * y + x ^ 2) * (y * z + y ^ 2)) := @solution
#print axioms solution

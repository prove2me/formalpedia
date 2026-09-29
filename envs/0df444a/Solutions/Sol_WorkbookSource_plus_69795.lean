-- Prove2me | solution 1 for WorkbookSource.plus_69795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:51.077927+00:00
-- url     : https://prove2.me/submissions/dd2fe2e6-a5fe-4de7-890a-1a7c9a94e41a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : z * (x + y + z) ≥ x * y) (h' : x * (x + y + z) ≥ y * z) (h'' : y * (x + y + z) ≥ z * x) : (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 2 ≥ 8 * x * y * z * (x + y + z) + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2   := by
  have h0 : 0 ≤ (11/4 : ℝ) * (1) * (-13*x^2/22 - x*y/2 - x*z/2 + 13*y^2/44 + y*z + 13*z^2/44)^2 := by positivity
  have h1 : 0 ≤ (33/16 : ℝ) * (1) * (-x*y + x*z - 13*y^2/22 + 13*z^2/22)^2 := by positivity
  have h2 : 0 ≤ (7/176 : ℝ) * (1) * (-x^2/2 - y^2/2 + z^2)^2 := by positivity
  have h3 : 0 ≤ (21/704 : ℝ) * (1) * (-x^2 + y^2)^2 := by positivity
  have h4 : 0 ≤ (3/8 : ℝ) * (y*z) * (-y + z)^2 := by positivity
  have h5 : 0 ≤ (3/8 : ℝ) * (x*z) * (-x + z)^2 := by positivity
  have h6 : 0 ≤ (3/8 : ℝ) * (x*y) * (-x + y)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : z * (x + y + z) ≥ x * y) (h' : x * (x + y + z) ≥ y * z) (h'' : y * (x + y + z) ≥ z * x), (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 2 ≥ 8 * x * y * z * (x + y + z) + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := @solution
#print axioms solution

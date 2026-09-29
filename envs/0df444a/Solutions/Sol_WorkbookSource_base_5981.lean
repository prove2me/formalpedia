-- Prove2me | solution 1 for WorkbookSource.base_5981
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:11.513855+00:00
-- url     : https://prove2.me/submissions/c33ac279-c0d1-4d5f-9efc-2b7af4ff9336

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 49 * (x + y + z) ^ 4 - 475 * (x + y + z) ^ 2 * (x*y + x*z + y*z) - 408 * (x + y + z) * x*y*z + 288 * (x + y + z) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) + 832 * (x*y + x*z + y*z) ^ 2 ≥ 0  := by
  have h0 : 0 ≤ (513 : ℝ) * (1) * (5*x^2/19 - x*y/2 - x*z/2 + y^2/114 + y*z - 31*z^2/114)^2 := by positivity
  have h1 : 0 ≤ (1539/4 : ℝ) * (1) * (-32*x^2/171 - x*y + x*z + 61*y^2/171 - 29*z^2/171)^2 := by positivity
  nlinarith only [h0, h1]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), 49 * (x + y + z) ^ 4 - 475 * (x + y + z) ^ 2 * (x*y + x*z + y*z) - 408 * (x + y + z) * x*y*z + 288 * (x + y + z) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) + 832 * (x*y + x*z + y*z) ^ 2 ≥ 0) := @solution
#print axioms solution

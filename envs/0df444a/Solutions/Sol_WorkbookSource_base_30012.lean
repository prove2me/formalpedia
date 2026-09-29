-- Prove2me | solution 1 for WorkbookSource.base_30012
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:04.507099+00:00
-- url     : https://prove2.me/submissions/c1290ca9-ebef-4748-9fb6-3018ec707b2d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : 10 * x * y * z ≤ x ^ 2 + y ^ 2 + z ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2  := by
  have helim : z = (-x - y + 1) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (x^2/2 + x*y/2 - x/2 - y^2/4 + y - 1/4)^2 + (3 : ℝ) * (x*y + x + y^2/2 - 1/2)^2 := by positivity
  have hid : ( x ^ 2 + y ^ 2 + z ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2  ) - ( 10 * x * y * z ) = (4 : ℝ) * (x^2/2 + x*y/2 - x/2 - y^2/4 + y - 1/4)^2 + (3 : ℝ) * (x*y + x + y^2/2 - 1/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1), 10 * x * y * z ≤ x ^ 2 + y ^ 2 + z ^ 2 + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := @solution
#print axioms solution

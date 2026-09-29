-- Prove2me | solution 1 for WorkbookSource.base_9070
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:29.135375+00:00
-- url     : https://prove2.me/submissions/570dcfd9-d461-4069-92f1-bc3014874e44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 2) : x * y * (x ^ 3 + y ^ 3) ≤ 8 / 3  := by
  have helim : y = (2 - x) := by linarith only [hxy]
  have hsum : 0 ≤ (24 : ℝ) * (-x^2/2 + x - 1/3)^2 := by positivity
  have hid : ( 8 / 3  ) - ( x * y * (x ^ 3 + y ^ 3) ) = (24 : ℝ) * (-x^2/2 + x - 1/3)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y = 2), x * y * (x ^ 3 + y ^ 3) ≤ 8 / 3) := @solution
#print axioms solution

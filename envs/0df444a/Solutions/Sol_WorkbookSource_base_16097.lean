-- Prove2me | solution 1 for WorkbookSource.base_16097
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:30.272509+00:00
-- url     : https://prove2.me/submissions/fe01a32a-c161-451f-9206-d153de6d34f0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a + b + c = 3) : (a + b - a * b) * (b + c - b * c) * (c + a - c * a) + a * b * c ≤ 9 / 4  := by
  have helim : c = (-a - b + 3) := by linarith only [ha]
  have hsum : 0 ≤ (16 : ℝ) * (-a^2*b/4 + a^2/4 - a*b^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4 + 3/8)^2 := by positivity
  have hid : ( 9 / 4  ) - ( (a + b - a * b) * (b + c - b * c) * (c + a - c * a) + a * b * c ) = (16 : ℝ) * (-a^2*b/4 + a^2/4 - a*b^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4 + 3/8)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a + b + c = 3), (a + b - a * b) * (b + c - b * c) * (c + a - c * a) + a * b * c ≤ 9 / 4) := @solution
#print axioms solution

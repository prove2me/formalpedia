-- Prove2me | solution 1 for WorkbookSource.base_957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:27.953293+00:00
-- url     : https://prove2.me/submissions/1e8d51fa-440e-4073-9688-a6ecbe91ad80

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : 2 * (a * b + a * c + b * c) ^ 2 + 8 / 27 ≥ a * b + a * c + b * c + 5 * a * b * c  := by
  have helim : c = (-a - b + 1) := by linarith only [hab]
  have hsum : 0 ≤ (49/12 : ℝ) * (24*a^2/49 + a*b - 37*a/147 + 24*b^2/49 - 37*b/147 - 23/441)^2 + (968/441 : ℝ) * (5*a^2/352 - a/48 - 15*b^2/22 + b - 799/3168)^2 + (5687/2592 : ℝ) * (-15*a^2/22 + a - 17/66)^2 := by positivity
  have hid : ( 2 * (a * b + a * c + b * c) ^ 2 + 8 / 27 ) - ( a * b + a * c + b * c + 5 * a * b * c  ) = (49/12 : ℝ) * (24*a^2/49 + a*b - 37*a/147 + 24*b^2/49 - 37*b/147 - 23/441)^2 + (968/441 : ℝ) * (5*a^2/352 - a/48 - 15*b^2/22 + b - 799/3168)^2 + (5687/2592 : ℝ) * (-15*a^2/22 + a - 17/66)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1), 2 * (a * b + a * c + b * c) ^ 2 + 8 / 27 ≥ a * b + a * c + b * c + 5 * a * b * c) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_35217
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:31.594398+00:00
-- url     : https://prove2.me/submissions/78d332e2-9944-4dc7-bc04-1a7dd99d2819

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z = 3) :
  (3 - x * y - y * z - z * x) ^ 3 ≥ (1 / 4) * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2  := by
  have helim : z = (-x - y + 3) := by linarith only [h]
  have hsum : 0 ≤ (108 : ℝ) * (-x^2*y/4 + x^2/4 - x*y^2/4 + x*y - 3*x/4 + y^2/4 - 3*y/4 + 1/2)^2 := by positivity
  have hid : (
  (3 - x * y - y * z - z * x) ^ 3 ) - ( (1 / 4) * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2  ) = (108 : ℝ) * (-x^2*y/4 + x^2/4 - x*y^2/4 + x*y - 3*x/4 + y^2/4 - 3*y/4 + 1/2)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z = 3), (3 - x * y - y * z - z * x) ^ 3 ≥ (1 / 4) * (y - z) ^ 2 * (z - x) ^ 2 * (x - y) ^ 2) := @solution
#print axioms solution

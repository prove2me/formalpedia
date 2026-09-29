-- Prove2me | solution 1 for WorkbookSource.base_41419
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:54.286037+00:00
-- url     : https://prove2.me/submissions/a1cc8d0f-af56-4337-9286-7eb8a410c34e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z u v w : ℝ) : (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) + (w - v) * (w + z) + (u - w) * (x + u) + (v - u) * (y + v) ≥ 0  := by
  have hsum : 0 ≤ (1 : ℝ) * (-u/2 - v/2 + w - x + y/2 + z/2)^2 + (3/4 : ℝ) * (-u + v + y - z)^2 := by positivity
  have hid : ( (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) + (w - v) * (w + z) + (u - w) * (x + u) + (v - u) * (y + v) ) - ( 0  ) = (1 : ℝ) * (-u/2 - v/2 + w - x + y/2 + z/2)^2 + (3/4 : ℝ) * (-u + v + y - z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z u v w : ℝ), (x - z) * (v - z) + (y - x) * (w - x) + (u - y) * (z - y) + (w - v) * (w + z) + (u - w) * (x + u) + (v - u) * (y + v) ≥ 0) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_28742
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:06.466635+00:00
-- url     : https://prove2.me/submissions/11e758bc-31ab-424f-8370-e58d370cc6b3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z = 1) :
  44 * (x * y + y * z + x * z) ≤ (3 * x + 4 * y + 5 * z) ^ 2  := by
  have helim : z = (-x - y + 1) := by linarith only [h]
  have hsum : 0 ≤ (48 : ℝ) * (x + y/2 - 2/3)^2 + (33 : ℝ) * (y - 1/3)^2 := by positivity
  have hid : ( (3 * x + 4 * y + 5 * z) ^ 2  ) - (
  44 * (x * y + y * z + x * z) ) = (48 : ℝ) * (x + y/2 - 2/3)^2 + (33 : ℝ) * (y - 1/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z = 1), 44 * (x * y + y * z + x * z) ≤ (3 * x + 4 * y + 5 * z) ^ 2) := @solution
#print axioms solution

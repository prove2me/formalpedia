-- Prove2me | solution 1 for WorkbookSource.base_30380
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:19.765021+00:00
-- url     : https://prove2.me/submissions/520fa2d6-68fc-4a67-9750-bb0de914bc7d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) : (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ≤ (x * y * z)^2 - 2 * x * y * z + 2  := by
  have hp0 : 0 ≤ x - 1 := by linarith only [hx]
  have hp1 : 0 ≤ y - 1 := by linarith only [hy]
  have hp2 : 0 ≤ z - 1 := by linarith only [hz]
  have hs : 0 ≤ (2 : ℝ) * ((x - 1)^2 * (y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (y - 1)^1 * (z - 1)^2) + (4 : ℝ) * ((x - 1)^2 * (y - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (y - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^2 * (z - 1)^2) + (4 : ℝ) * ((x - 1)^1 * (y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^2) + (4 : ℝ) * ((x - 1)^1 * (y - 1)^1 * (z - 1)^2) + (6 : ℝ) * ((x - 1)^1 * (y - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (z - 1)^2) + (2 : ℝ) * ((x - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((y - 1)^1 * (z - 1)^2) + (2 : ℝ) * ((y - 1)^1 * (z - 1)^1) := by positivity
  have hi : ( (x * y * z)^2 - 2 * x * y * z + 2  ) - ( (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ) = (2 : ℝ) * ((x - 1)^2 * (y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (y - 1)^1 * (z - 1)^2) + (4 : ℝ) * ((x - 1)^2 * (y - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (y - 1)^1) + (2 : ℝ) * ((x - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^2 * (z - 1)^2) + (4 : ℝ) * ((x - 1)^1 * (y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^2) + (4 : ℝ) * ((x - 1)^1 * (y - 1)^1 * (z - 1)^2) + (6 : ℝ) * ((x - 1)^1 * (y - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (y - 1)^1) + (2 : ℝ) * ((x - 1)^1 * (z - 1)^2) + (2 : ℝ) * ((x - 1)^1 * (z - 1)^1) + (2 : ℝ) * ((y - 1)^2 * (z - 1)^1) + (2 : ℝ) * ((y - 1)^1 * (z - 1)^2) + (2 : ℝ) * ((y - 1)^1 * (z - 1)^1) := by
    ring
  linarith only [hs,hi]
example : (∀ (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z), (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ≤ (x * y * z)^2 - 2 * x * y * z + 2) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_12152
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:47.210163+00:00
-- url     : https://prove2.me/submissions/ace9136f-9839-484a-b68c-6593119f3d89

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c k : ℝ) (h : k ≥ 0) : a^2 + 2 * b^2 + 2 * c^2 + k * a + 7 * k^2 / 24 ≥ a * b + 2 * b * c + c * a + k * c  := by
  have hw0 : 0 ≤ (k) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a/4 - b/2 + c - k/4)^2 + (3/2 : ℝ) * (1) * (-a/2 + b - k/6)^2 + (1/2 : ℝ) * (1) * (a + k/2)^2 := by positivity
  have hid : ( a^2 + 2 * b^2 + 2 * c^2 + k * a + 7 * k^2 / 24 ) - ( a * b + 2 * b * c + c * a + k * c  ) = (2 : ℝ) * (1) * (-a/4 - b/2 + c - k/4)^2 + (3/2 : ℝ) * (1) * (-a/2 + b - k/6)^2 + (1/2 : ℝ) * (1) * (a + k/2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c k : ℝ) (h : k ≥ 0), a^2 + 2 * b^2 + 2 * c^2 + k * a + 7 * k^2 / 24 ≥ a * b + 2 * b * c + c * a + k * c) := @solution
#print axioms solution

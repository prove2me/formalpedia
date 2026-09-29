-- Prove2me | solution 1 for WorkbookSource.base_4616
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:27.404255+00:00
-- url     : https://prove2.me/submissions/ec0851ec-bdd9-4139-a759-442456d61436

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) : 2 * (a^4 + b^4 + c^4) + 36 ≥ 7 * (a^3 + b^3 + c^3) + 21 * a * b * c  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (39 : ℝ) * (a^2/13 - 6*a*b/13 + a/26 - 4*b^2/13 + b - 9/26)^2 + (2025/52 : ℝ) * (-14*a^2/45 - 4*a*b/9 + a + 4*b^2/45 - 1/3)^2 := by positivity
  have hid : ( 2 * (a^4 + b^4 + c^4) + 36 ) - ( 7 * (a^3 + b^3 + c^3) + 21 * a * b * c  ) = (39 : ℝ) * (a^2/13 - 6*a*b/13 + a/26 - 4*b^2/13 + b - 9/26)^2 + (2025/52 : ℝ) * (-14*a^2/45 - 4*a*b/9 + a + 4*b^2/45 - 1/3)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), 2 * (a^4 + b^4 + c^4) + 36 ≥ 7 * (a^3 + b^3 + c^3) + 21 * a * b * c) := @solution
#print axioms solution

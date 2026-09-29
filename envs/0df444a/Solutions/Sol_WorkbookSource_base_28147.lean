-- Prove2me | solution 1 for WorkbookSource.base_28147
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:05.785215+00:00
-- url     : https://prove2.me/submissions/2fd4c57b-9dec-453c-b48c-ebd32f7cd5a2

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 0) : a^4 + b^4 + c^4 + 6*a*b*c + 12 ≥ 3 * (a^2 + b^2 + c^2)  := by
  have helim : c = (-a - b) := by linarith only [h]
  have hsum : 0 ≤ (12 : ℝ) * (-a^2/3 - a*b/3 - b^2/3 + 1)^2 + (8/3 : ℝ) * (a^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4)^2 + (1/2 : ℝ) * (-a^2 - a + b^2 + b)^2 := by positivity
  have hid : ( a^4 + b^4 + c^4 + 6*a*b*c + 12 ) - ( 3 * (a^2 + b^2 + c^2)  ) = (12 : ℝ) * (-a^2/3 - a*b/3 - b^2/3 + 1)^2 + (8/3 : ℝ) * (a^2/4 + a*b - 3*a/4 + b^2/4 - 3*b/4)^2 + (1/2 : ℝ) * (-a^2 - a + b^2 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 0), a^4 + b^4 + c^4 + 6*a*b*c + 12 ≥ 3 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution

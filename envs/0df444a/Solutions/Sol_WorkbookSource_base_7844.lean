-- Prove2me | solution 1 for WorkbookSource.base_7844
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:27.95419+00:00
-- url     : https://prove2.me/submissions/18231ffb-82e9-4481-b26b-e9292566ce4c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a + b + c + d = 4) : 13 * (a^2 + b^2 + c^2 + d^2)^2 ≥ 12 * (a^4 + b^4 + c^4 + d^4) + 160  := by
  have helim : d = (-a - b - c + 4) := by linarith only [h]
  have hsum : 0 ≤ (464 : ℝ) * (a^2/58 - a*b/29 - 17*a*c/58 + 3*a/58 + b^2/58 - 17*b*c/58 + 3*b/58 - 7*c^2/29 + c - 8/29)^2 + (13420/29 : ℝ) * (a^2/61 - 196*a*b/671 - 13*a*c/671 + 3*a/61 - 163*b^2/671 - 17*b*c/61 + b + 20*c^2/671 - 16/61)^2 + (28160/61 : ℝ) * (-43*a^2/176 - 49*a*b/176 - 49*a*c/176 + a + 5*b^2/176 - b*c/176 + 5*c^2/176 - 1/4)^2 + (200/11 : ℝ) * (a^2/10 - a*b/2 - a*c/2 - b^2/20 + b*c - c^2/20)^2 + (150/11 : ℝ) * (-a*b + a*c + b^2/10 - c^2/10)^2 := by positivity
  have hid : ( 13 * (a^2 + b^2 + c^2 + d^2)^2 ) - ( 12 * (a^4 + b^4 + c^4 + d^4) + 160  ) = (464 : ℝ) * (a^2/58 - a*b/29 - 17*a*c/58 + 3*a/58 + b^2/58 - 17*b*c/58 + 3*b/58 - 7*c^2/29 + c - 8/29)^2 + (13420/29 : ℝ) * (a^2/61 - 196*a*b/671 - 13*a*c/671 + 3*a/61 - 163*b^2/671 - 17*b*c/61 + b + 20*c^2/671 - 16/61)^2 + (28160/61 : ℝ) * (-43*a^2/176 - 49*a*b/176 - 49*a*c/176 + a + 5*b^2/176 - b*c/176 + 5*c^2/176 - 1/4)^2 + (200/11 : ℝ) * (a^2/10 - a*b/2 - a*c/2 - b^2/20 + b*c - c^2/20)^2 + (150/11 : ℝ) * (-a*b + a*c + b^2/10 - c^2/10)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a + b + c + d = 4), 13 * (a^2 + b^2 + c^2 + d^2)^2 ≥ 12 * (a^4 + b^4 + c^4 + d^4) + 160) := @solution
#print axioms solution

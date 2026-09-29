-- Prove2me | solution 1 for WorkbookSource.base_15121
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:31.390073+00:00
-- url     : https://prove2.me/submissions/35e343bf-b0a1-4400-899c-b56f5e59c931

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 1) : 1 + 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 4 * (a ^ 3 + b ^ 3 + c ^ 3)  := by
  have helim : c = (-a - b + 1) := by linarith only [h]
  have hsum : 0 ≤ (6 : ℝ) * (-a^2 - a*b + a - b^2 + b)^2 := by positivity
  have hid : ( 1 + 3 * (a ^ 4 + b ^ 4 + c ^ 4) ) - ( 4 * (a ^ 3 + b ^ 3 + c ^ 3)  ) = (6 : ℝ) * (-a^2 - a*b + a - b^2 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 1), 1 + 3 * (a ^ 4 + b ^ 4 + c ^ 4) ≥ 4 * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution

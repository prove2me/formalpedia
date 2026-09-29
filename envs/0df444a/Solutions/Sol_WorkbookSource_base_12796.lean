-- Prove2me | solution 1 for WorkbookSource.base_12796
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:30.145411+00:00
-- url     : https://prove2.me/submissions/4077b38a-7958-4f79-9421-0c6ac61ac9f4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (habc : a + b + c = 1) : 1 + 18 * (a ^ 4 + b ^ 4 + c ^ 4) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3)  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hsum : 0 ≤ (36 : ℝ) * (-a^2 - a*b + a - b^2 + b - 1/6)^2 := by positivity
  have hid : ( 1 + 18 * (a ^ 4 + b ^ 4 + c ^ 4) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ) - ( 24 * (a ^ 3 + b ^ 3 + c ^ 3)  ) = (36 : ℝ) * (-a^2 - a*b + a - b^2 + b - 1/6)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (habc : a + b + c = 1), 1 + 18 * (a ^ 4 + b ^ 4 + c ^ 4) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 24 * (a ^ 3 + b ^ 3 + c ^ 3)) := @solution
#print axioms solution

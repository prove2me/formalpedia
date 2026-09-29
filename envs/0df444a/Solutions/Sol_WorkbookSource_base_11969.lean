-- Prove2me | solution 1 for WorkbookSource.base_11969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:46:29.407183+00:00
-- url     : https://prove2.me/submissions/b0019268-93e6-48ac-87ab-8d0b4c1632f3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) :
  7 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 3 ≥ (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4  := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (432 : ℝ) * (a^2/12 + a*b/3 - 3*a/4 + b^2/12 - 3*b/4 + 1)^2 + (9 : ℝ) * (a^2 - a - b^2 + b)^2 := by positivity
  have hid : (
  7 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 3 ) - ( (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4  ) = (432 : ℝ) * (a^2/12 + a*b/3 - 3*a/4 + b^2/12 - 3*b/4 + 1)^2 + (9 : ℝ) * (a^2 - a - b^2 + b)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), 7 * (a ^ 4 + b ^ 4 + c ^ 4) + (a + b + c) ^ 3 ≥ (a + b) ^ 4 + (b + c) ^ 4 + (c + a) ^ 4) := @solution
#print axioms solution

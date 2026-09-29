-- Prove2me | solution 1 for WorkbookSource.plus_43984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:13.95712+00:00
-- url     : https://prove2.me/submissions/cc5a1787-aeeb-4684-a916-90d28d83b305

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 3) : (a^2 + b^2 + c^2)^2 + 3 * a * b * c ≥ 4 * (a^2 + b^2 + c^2)   := by
  have helim : c = (-a - b + 3) := by linarith only [h]
  have hsum : 0 ≤ (45 : ℝ) * (4*a^2/15 + a*b/3 - 14*a/15 + 4*b^2/15 - 14*b/15 + 1)^2 + (4/5 : ℝ) * (-3*a^2/8 + 3*a/8 - b^2 + b)^2 + (11/16 : ℝ) * (-a^2 + a)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2)^2 + 3 * a * b * c ) - ( 4 * (a^2 + b^2 + c^2)   ) = (45 : ℝ) * (4*a^2/15 + a*b/3 - 14*a/15 + 4*b^2/15 - 14*b/15 + 1)^2 + (4/5 : ℝ) * (-3*a^2/8 + 3*a/8 - b^2 + b)^2 + (11/16 : ℝ) * (-a^2 + a)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 3), (a^2 + b^2 + c^2)^2 + 3 * a * b * c ≥ 4 * (a^2 + b^2 + c^2)) := @solution
#print axioms solution

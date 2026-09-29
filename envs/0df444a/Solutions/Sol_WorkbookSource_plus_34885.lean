-- Prove2me | solution 1 for WorkbookSource.plus_34885
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:07.09091+00:00
-- url     : https://prove2.me/submissions/d0b37bda-1814-411d-805e-024cff065e08

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 + b^2 * c^2 + 10 ≥ 4 * (b * c + c * a + a * b)   := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (11 : ℝ) * (-3*a*b/11 + a/11 - 3*b^2/11 + b - 6/11)^2 + (74/11 : ℝ) * (-7*a*b/74 - 30*a/37 - 7*b^2/74 + 1)^2 + (18/37 : ℝ) * (-a*b/2 + a - b^2/2)^2 := by positivity
  have hid : ( a^2 + b^2 * c^2 + 10 ) - ( 4 * (b * c + c * a + a * b)   ) = (11 : ℝ) * (-3*a*b/11 + a/11 - 3*b^2/11 + b - 6/11)^2 + (74/11 : ℝ) * (-7*a*b/74 - 30*a/37 - 7*b^2/74 + 1)^2 + (18/37 : ℝ) * (-a*b/2 + a - b^2/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a^2 + b^2 * c^2 + 10 ≥ 4 * (b * c + c * a + a * b)) := @solution
#print axioms solution

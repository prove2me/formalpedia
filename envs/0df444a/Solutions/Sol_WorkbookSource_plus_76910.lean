-- Prove2me | solution 1 for WorkbookSource.plus_76910
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:07.75178+00:00
-- url     : https://prove2.me/submissions/09df4d92-6b13-46d1-80c9-24ade4c4861f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a^4 + b^4 + c^4 + 8 * (a * b + b * c + c * a) ≥ 27   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hsum : 0 ≤ (54 : ℝ) * (a^2/9 + a*b/3 - 7*a/9 + b^2/9 - 7*b/9 + 1)^2 + (4/3 : ℝ) * (a^2/2 - a/2 - b^2 + b)^2 + (1 : ℝ) * (-a^2 + a)^2 := by positivity
  have hid : ( a^4 + b^4 + c^4 + 8 * (a * b + b * c + c * a) ) - ( 27   ) = (54 : ℝ) * (a^2/9 + a*b/3 - 7*a/9 + b^2/9 - 7*b/9 + 1)^2 + (4/3 : ℝ) * (a^2/2 - a/2 - b^2 + b)^2 + (1 : ℝ) * (-a^2 + a)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a^4 + b^4 + c^4 + 8 * (a * b + b * c + c * a) ≥ 27) := @solution
#print axioms solution

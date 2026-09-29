-- Prove2me | solution 1 for WorkbookSource.plus_12056
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:10.753726+00:00
-- url     : https://prove2.me/submissions/e3b9a6c5-ec8a-497c-b58f-d8e4a3141a45

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + a + b*c + d ≥ 7   := by
  have helim : d = (-a - b - c + 4) := by linarith only [habc]
  have hsum : 0 ≤ (13 : ℝ) * (-4*a/13 - 9*b/26 - 9*c/26 + 1)^2 + (10/13 : ℝ) * (a - b/2 - c/2)^2 + (1/4 : ℝ) * (-b + c)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + d^2 + a + b*c + d ) - ( 7   ) = (13 : ℝ) * (-4*a/13 - 9*b/26 - 9*c/26 + 1)^2 + (10/13 : ℝ) * (a - b/2 - c/2)^2 + (1/4 : ℝ) * (-b + c)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4), a^2 + b^2 + c^2 + d^2 + a + b*c + d ≥ 7) := @solution
#print axioms solution

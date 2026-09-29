-- Prove2me | solution 1 for WorkbookSource.plus_37409
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:02.995718+00:00
-- url     : https://prove2.me/submissions/793e2183-effa-41e0-b083-d51e3719edc6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ≤ 2   := by
  have helim : c = (-a - b + 2) := by linarith only [habc]
  have hslack : 0 ≤ (-a - b + 2) := by linarith only [helim, hc]
  have hsum : 0 ≤ (8 : ℝ) * (1) * (-a^2/2 - a*b/2 + a - b^2/2 + b - 1/2)^2 + (2 : ℝ) * ((a) * (b) * (-a - b + 2)) * (1)^2 := by positivity
  have hid : ( 2   ) - ( a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ) = (8 : ℝ) * (1) * (-a^2/2 - a*b/2 + a - b^2/2 + b - 1/2)^2 + (2 : ℝ) * ((a) * (b) * (-a - b + 2)) * (1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2), a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2) ≤ 2) := @solution
#print axioms solution

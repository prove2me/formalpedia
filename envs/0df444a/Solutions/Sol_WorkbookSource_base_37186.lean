-- Prove2me | solution 1 for WorkbookSource.base_37186
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:32.148083+00:00
-- url     : https://prove2.me/submissions/f9b3d8c2-e3eb-40e4-9e83-5c1c5cc200d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : (a^2 + b^2 + c^2)^2 - 2 * (a^3 + b^3 + c^3) ≥ 189 / 64  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (81/2 : ℝ) * (-2*a^2/27 - 4*a*b/9 + a/2 - 8*b^2/27 + b - 2/3)^2 + (243/8 : ℝ) * (-28*a^2/81 - 8*a*b/27 + a + 8*b^2/81 - 4/9)^2 + (4/3 : ℝ) * (-a^2/3 + a*b - b^2/3 - 3/16)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2)^2 - 2 * (a^3 + b^3 + c^3) ) - ( 189 / 64  ) = (81/2 : ℝ) * (-2*a^2/27 - 4*a*b/9 + a/2 - 8*b^2/27 + b - 2/3)^2 + (243/8 : ℝ) * (-28*a^2/81 - 8*a*b/27 + a + 8*b^2/81 - 4/9)^2 + (4/3 : ℝ) * (-a^2/3 + a*b - b^2/3 - 3/16)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), (a^2 + b^2 + c^2)^2 - 2 * (a^3 + b^3 + c^3) ≥ 189 / 64) := @solution
#print axioms solution

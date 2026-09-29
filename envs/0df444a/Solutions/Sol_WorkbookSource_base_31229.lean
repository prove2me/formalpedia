-- Prove2me | solution 1 for WorkbookSource.base_31229
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:05.093976+00:00
-- url     : https://prove2.me/submissions/cb388716-d700-4042-aaa0-06e3419befa9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 9) : 227 + (a * b + b * c + c * a - 23)^2 ≥ 2 * (a^2 * b + b^2 * c + c^2 * a) + 3 * a * b * c  := by
  have helim : c = (-a - b + 9) := by linarith only [habc]
  have hsum : 0 ≤ (756 : ℝ) * (a^2/42 + a*b/14 - 8*a/21 + b^2/84 - 23*b/84 + 1)^2 + (961/28 : ℝ) * (4*a^2/31 - 2*a*b/31 - 22*a/31 - 5*b^2/31 + b)^2 := by positivity
  have hid : ( 227 + (a * b + b * c + c * a - 23)^2 ) - ( 2 * (a^2 * b + b^2 * c + c^2 * a) + 3 * a * b * c  ) = (756 : ℝ) * (a^2/42 + a*b/14 - 8*a/21 + b^2/84 - 23*b/84 + 1)^2 + (961/28 : ℝ) * (4*a^2/31 - 2*a*b/31 - 22*a/31 - 5*b^2/31 + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 9), 227 + (a * b + b * c + c * a - 23)^2 ≥ 2 * (a^2 * b + b^2 * c + c^2 * a) + 3 * a * b * c) := @solution
#print axioms solution

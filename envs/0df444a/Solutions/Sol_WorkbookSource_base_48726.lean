-- Prove2me | solution 1 for WorkbookSource.base_48726
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:01.790021+00:00
-- url     : https://prove2.me/submissions/06ae7fb7-df35-42ad-b72f-551a1dbb6780

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : a + 4 * a * b * c ≤ 2  := by
  have helim : c = (-a - b + 2) := by linarith only [habc]
  have hslack : 0 ≤ (-a - b + 2) := by linarith only [helim, hc]
  have hsum : 0 ≤ (1 : ℝ) * ((-a - b + 2)) * (1 - a)^2 + (1 : ℝ) * ((b)) * (1 - a)^2 + (4 : ℝ) * ((a)) * (-a/2 - b + 1)^2 := by positivity
  have hid : ( 2  ) - ( a + 4 * a * b * c ) = (1 : ℝ) * ((-a - b + 2)) * (1 - a)^2 + (1 : ℝ) * ((b)) * (1 - a)^2 + (4 : ℝ) * ((a)) * (-a/2 - b + 1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2), a + 4 * a * b * c ≤ 2) := @solution
#print axioms solution

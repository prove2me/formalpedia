-- Prove2me | solution 1 for WorkbookSource.base_12079
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:37:00.357296+00:00
-- url     : https://prove2.me/submissions/456439df-9464-41b8-987d-a6a6d53416a4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a^2 * b + b^2 * c + c^2 * a ≤ 4  := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b + 3) := by linarith only [helim, hc]
  have hsum : 0 ≤ (4/3 : ℝ) * ((-a - b + 3)) * (-a - b/2 + 1)^2 + (16/3 : ℝ) * ((b)) * (-a/4 - b/2 + 1)^2 + (1/3 : ℝ) * ((a)) * (-a + b + 1)^2 := by positivity
  have hid : ( 4  ) - ( a^2 * b + b^2 * c + c^2 * a ) = (4/3 : ℝ) * ((-a - b + 3)) * (-a - b/2 + 1)^2 + (16/3 : ℝ) * ((b)) * (-a/4 - b/2 + 1)^2 + (1/3 : ℝ) * ((a)) * (-a + b + 1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), a^2 * b + b^2 * c + c^2 * a ≤ 4) := @solution
#print axioms solution

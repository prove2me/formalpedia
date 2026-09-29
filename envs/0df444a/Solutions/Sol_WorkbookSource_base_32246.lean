-- Prove2me | solution 1 for WorkbookSource.base_32246
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:37:19.263083+00:00
-- url     : https://prove2.me/submissions/4f5437c7-1fc7-4718-9b74-eab60d2aa57f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : 2 * (b * c + 3 * a) ^ 2 + 2 * (c * a + 3 * b) ^ 2 + 2 * (a * b + 3 * c) ^ 2 + (2 * a * b + 2 * b * c + 2 * c * a + 3) ^ 2 ≥ 147  := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b + 3) := by linarith only [helim, hc]
  have hsum : 0 ≤ (54 : ℝ) * (1) * (-a^2/3 - a*b/3 + a - b^2/3 + b - 2/3)^2 + (24 : ℝ) * ((a) * (b) * (-a - b + 3)) * (1)^2 := by positivity
  have hid : ( 2 * (b * c + 3 * a) ^ 2 + 2 * (c * a + 3 * b) ^ 2 + 2 * (a * b + 3 * c) ^ 2 + (2 * a * b + 2 * b * c + 2 * c * a + 3) ^ 2 ) - ( 147  ) = (54 : ℝ) * (1) * (-a^2/3 - a*b/3 + a - b^2/3 + b - 2/3)^2 + (24 : ℝ) * ((a) * (b) * (-a - b + 3)) * (1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), 2 * (b * c + 3 * a) ^ 2 + 2 * (c * a + 3 * b) ^ 2 + 2 * (a * b + 3 * c) ^ 2 + (2 * a * b + 2 * b * c + 2 * c * a + 3) ^ 2 ≥ 147) := @solution
#print axioms solution

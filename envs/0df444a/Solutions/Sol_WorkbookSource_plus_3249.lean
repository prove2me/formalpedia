-- Prove2me | solution 1 for WorkbookSource.plus_3249
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:06.453702+00:00
-- url     : https://prove2.me/submissions/3b556556-dd2b-47f4-959b-24fef6b38080

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : 4 * (a * b + b * c + a * c) ^ 2 + 6 * a * b * c + 1 ≥ 5 * (a * b + b * c + a * c)   := by
  have helim : c = (-a - b + 1) := by linarith only [hab]
  have hsum : 0 ≤ (16 : ℝ) * (a^2/4 + a*b - 5*a/8 + b^2/4 - 5*b/8 + 1/4)^2 + (3 : ℝ) * (-a^2 + a/2 + b^2 - b/2)^2 := by positivity
  have hid : ( 4 * (a * b + b * c + a * c) ^ 2 + 6 * a * b * c + 1 ) - ( 5 * (a * b + b * c + a * c)   ) = (16 : ℝ) * (a^2/4 + a*b - 5*a/8 + b^2/4 - 5*b/8 + 1/4)^2 + (3 : ℝ) * (-a^2 + a/2 + b^2 - b/2)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1), 4 * (a * b + b * c + a * c) ^ 2 + 6 * a * b * c + 1 ≥ 5 * (a * b + b * c + a * c)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_6731
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:36:59.811877+00:00
-- url     : https://prove2.me/submissions/5a66d9de-a926-42eb-8c24-b3ba16f3e5d1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a^2 * b * c + b^2 * c * d + c^2 * d * a + d^2 * a * b ≤ 4  := by
  have helim : d = (-a - b - c + 4) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b - c + 4) := by linarith only [helim, hd]
  have hsum : 0 ≤ (16 : ℝ) * (1) * (-a*b/4 + a*c/4 - b^2/4 - b*c/4 + b - 1/2)^2 + (4 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/2 - b/2 + 1)^2 + (4 : ℝ) * ((a) * (c)) * (-b/2 - c/2 + 1)^2 := by positivity
  have hid : ( 4  ) - ( a^2 * b * c + b^2 * c * d + c^2 * d * a + d^2 * a * b ) = (16 : ℝ) * (1) * (-a*b/4 + a*c/4 - b^2/4 - b*c/4 + b - 1/2)^2 + (4 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/2 - b/2 + 1)^2 + (4 : ℝ) * ((a) * (c)) * (-b/2 - c/2 + 1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4), a^2 * b * c + b^2 * c * d + c^2 * d * a + d^2 * a * b ≤ 4) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_38151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:01.042786+00:00
-- url     : https://prove2.me/submissions/5a7aa03d-6d44-438a-aa01-8b5c2f014750

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 5) : a^2 * b + c^2 * a + 2 * a * b * c ≤ 20  := by
  have helim : c = (-a - b + 5) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b + 5) := by linarith only [helim, hc]
  have hsum : 0 ≤ (4 : ℝ) * ((-a - b + 5)) * (-11*a/20 + b/10 + 1)^2 + (3/25 : ℝ) * ((-a - b + 5)) * (-a/2 + b)^2 + (4/25 : ℝ) * ((b)) * (-a/2 + b)^2 + (1 : ℝ) * ((a)) * (-3*a/10 - 2*b/5 + 1)^2 + (3/5 : ℝ) * ((a)) * (-a/2 + b)^2 := by positivity
  have hid : ( 20  ) - ( a^2 * b + c^2 * a + 2 * a * b * c ) = (4 : ℝ) * ((-a - b + 5)) * (-11*a/20 + b/10 + 1)^2 + (3/25 : ℝ) * ((-a - b + 5)) * (-a/2 + b)^2 + (4/25 : ℝ) * ((b)) * (-a/2 + b)^2 + (1 : ℝ) * ((a)) * (-3*a/10 - 2*b/5 + 1)^2 + (3/5 : ℝ) * ((a)) * (-a/2 + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 5), a^2 * b + c^2 * a + 2 * a * b * c ≤ 20) := @solution
#print axioms solution

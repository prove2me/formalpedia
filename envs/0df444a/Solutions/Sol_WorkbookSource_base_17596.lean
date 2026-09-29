-- Prove2me | solution 1 for WorkbookSource.base_17596
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:59:03.625709+00:00
-- url     : https://prove2.me/submissions/c6c69dff-8430-4536-a8ef-19ce7dc1533a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) (h : a * b + b * c + c * a > 0) : 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * a * b * c ≤ (6 - a * b - b * c - c * a) ^ 2  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hsum : 0 ≤ (57 : ℝ) * (-4*a^2/19 - 7*a*b/19 + a + b^2/38 + 13*b/38 - 15/19)^2 + (1089/76 : ℝ) * (2*a^2/11 - 6*a*b/11 - 5*b^2/11 + b - 2/11)^2 := by positivity
  have hid : ( (6 - a * b - b * c - c * a) ^ 2  ) - ( 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * a * b * c ) = (57 : ℝ) * (-4*a^2/19 - 7*a*b/19 + a + b^2/38 + 13*b/38 - 15/19)^2 + (1089/76 : ℝ) * (2*a^2/11 - 6*a*b/11 - 5*b^2/11 + b - 2/11)^2 := by
    rw [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) (h : a * b + b * c + c * a > 0), 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 3 * a * b * c ≤ (6 - a * b - b * c - c * a) ^ 2) := @solution
#print axioms solution

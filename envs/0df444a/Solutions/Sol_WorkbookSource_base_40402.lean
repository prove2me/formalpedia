-- Prove2me | solution 1 for WorkbookSource.base_40402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:04.771862+00:00
-- url     : https://prove2.me/submissions/3d97a86f-b2c5-4524-aad6-8062bba1c1d4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 5) : 2 * a + 2 * a * b + a * b * c ≤ 18  := by
  have helim : c = (-a - b + 5) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b + 5) := by linarith only [helim, hc]
  have hsum : 0 ≤ (18/5 : ℝ) * ((-a - b + 5)) * (-43*a/108 + 7*b/72 + 1)^2 + (19/288 : ℝ) * ((-a - b + 5)) * (-2*a/3 + b)^2 + (1/10 : ℝ) * ((b)) * (-a + b + 1)^2 + (239/15 : ℝ) * ((a)) * (-44*a/239 - 107*b/478 + 1)^2 + (129/956 : ℝ) * ((a)) * (-2*a/3 + b)^2 := by positivity
  have hid : ( 18  ) - ( 2 * a + 2 * a * b + a * b * c ) = (18/5 : ℝ) * ((-a - b + 5)) * (-43*a/108 + 7*b/72 + 1)^2 + (19/288 : ℝ) * ((-a - b + 5)) * (-2*a/3 + b)^2 + (1/10 : ℝ) * ((b)) * (-a + b + 1)^2 + (239/15 : ℝ) * ((a)) * (-44*a/239 - 107*b/478 + 1)^2 + (129/956 : ℝ) * ((a)) * (-2*a/3 + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 5), 2 * a + 2 * a * b + a * b * c ≤ 18) := @solution
#print axioms solution

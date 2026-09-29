-- Prove2me | solution 1 for WorkbookSource.base_43233
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:37:21.387618+00:00
-- url     : https://prove2.me/submissions/e21b0f8e-2099-49fe-aed3-6a703dd4766d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1) : 5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + 12 * (a * b * c + b * c * d + c * d * a + d * a * b) ≥ 1  := by
  have helim : d = (-a - b - c + 1) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b - c + 1) := by linarith only [helim, hd]
  have hsum : 0 ≤ (9 : ℝ) * ((-a - b - c + 1)) * (a + b + c - 2/3)^2 + (9 : ℝ) * ((c)) * (c - 1/3)^2 + (9 : ℝ) * ((b)) * (b - 1/3)^2 + (9 : ℝ) * ((a)) * (a - 1/3)^2 := by positivity
  have hid : ( 5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + 12 * (a * b * c + b * c * d + c * d * a + d * a * b) ) - ( 1  ) = (9 : ℝ) * ((-a - b - c + 1)) * (a + b + c - 2/3)^2 + (9 : ℝ) * ((c)) * (c - 1/3)^2 + (9 : ℝ) * ((b)) * (b - 1/3)^2 + (9 : ℝ) * ((a)) * (a - 1/3)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 1), 5 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) + 12 * (a * b * c + b * c * d + c * d * a + d * a * b) ≥ 1) := @solution
#print axioms solution

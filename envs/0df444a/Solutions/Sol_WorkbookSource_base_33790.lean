-- Prove2me | solution 1 for WorkbookSource.base_33790
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:37:19.962448+00:00
-- url     : https://prove2.me/submissions/cc8fb6f4-6b2c-4ad6-9839-f61de5fdec5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a + b + c + d = 1) : a * b + a * c + a * d + b * c + b * d + c * d + 48 * a * b * c * d ≥ 9 * (a * b * c + a * b * d + a * c * d + b * c * d)  := by
  have helim : d = (-a - b - c + 1) := by linarith only [habc]
  have hslack : 0 ≤ (-a - b - c + 1) := by linarith only [helim, hd]
  have hsum : 0 ≤ (16 : ℝ) * (1) * (-a^2/2 - a*b/2 - a*c/2 + a/2 + b^2/4 + b*c - b/4 + c^2/4 - c/4)^2 + (12 : ℝ) * (1) * (-a*b + a*c - b^2/2 + b/2 + c^2/2 - c/2)^2 + (4 : ℝ) * ((c) * (-a - b - c + 1)) * (a/2 + b/2 + c - 1/2)^2 + (4 : ℝ) * ((b) * (-a - b - c + 1)) * (a/2 + b + c/2 - 1/2)^2 + (1 : ℝ) * ((b) * (c)) * (-b + c)^2 + (4 : ℝ) * ((a) * (-a - b - c + 1)) * (a + b/2 + c/2 - 1/2)^2 + (1 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( a * b + a * c + a * d + b * c + b * d + c * d + 48 * a * b * c * d ) - ( 9 * (a * b * c + a * b * d + a * c * d + b * c * d)  ) = (16 : ℝ) * (1) * (-a^2/2 - a*b/2 - a*c/2 + a/2 + b^2/4 + b*c - b/4 + c^2/4 - c/4)^2 + (12 : ℝ) * (1) * (-a*b + a*c - b^2/2 + b/2 + c^2/2 - c/2)^2 + (4 : ℝ) * ((c) * (-a - b - c + 1)) * (a/2 + b/2 + c - 1/2)^2 + (4 : ℝ) * ((b) * (-a - b - c + 1)) * (a/2 + b + c/2 - 1/2)^2 + (1 : ℝ) * ((b) * (c)) * (-b + c)^2 + (4 : ℝ) * ((a) * (-a - b - c + 1)) * (a + b/2 + c/2 - 1/2)^2 + (1 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1 : ℝ) * ((a) * (b)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (habc : a + b + c + d = 1), a * b + a * c + a * d + b * c + b * d + c * d + 48 * a * b * c * d ≥ 9 * (a * b * c + a * b * d + a * c * d + b * c * d)) := @solution
#print axioms solution

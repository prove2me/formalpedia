-- Prove2me | solution 1 for WorkbookSource.base_41246
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:07.408558+00:00
-- url     : https://prove2.me/submissions/2641851c-7bcf-4f40-8101-ef7daa474f32

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c ≤ 8) : a^2 + (b - 6) * a - (b - 2) * c ≥ -9  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a - b - c + 8) := by linarith only [habc]
  have hsum : 0 ≤ (9 : ℝ) * (1) * (-a/3 - b/4 + c/12 + 1)^2 + (1/16 : ℝ) * ((c) * (-a - b - c + 8)) * (1)^2 + (9/16 : ℝ) * ((b) * (-a - b - c + 8)) * (1)^2 + (9/16 : ℝ) * ((a) * (c)) * (1)^2 + (1/16 : ℝ) * ((a) * (b)) * (1)^2 := by positivity
  have hid : ( a^2 + (b - 6) * a - (b - 2) * c ) - ( -9  ) = (9 : ℝ) * (1) * (-a/3 - b/4 + c/12 + 1)^2 + (1/16 : ℝ) * ((c) * (-a - b - c + 8)) * (1)^2 + (9/16 : ℝ) * ((b) * (-a - b - c + 8)) * (1)^2 + (9/16 : ℝ) * ((a) * (c)) * (1)^2 + (1/16 : ℝ) * ((a) * (b)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c ≤ 8), a^2 + (b - 6) * a - (b - 2) * c ≥ -9) := @solution
#print axioms solution

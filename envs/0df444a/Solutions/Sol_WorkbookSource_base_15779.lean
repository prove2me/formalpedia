-- Prove2me | solution 1 for WorkbookSource.base_15779
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:47.991194+00:00
-- url     : https://prove2.me/submissions/9205b0cd-ba80-4b19-b21f-8188ad296d48

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 5) : a * b + a + 5 * b ≤ 13  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (a^2 + b^2 - 5) := by linarith only [hab]
  have hw3 : 0 ≤ (-a^2 - b^2 + 5) := by linarith only [hab]
  have hsum : 0 ≤ (11/2 : ℝ) * (1) * (-a/11 - 5*b/11 + 1)^2 + (16/11 : ℝ) * (1) * (a - b/2)^2 + (3/2 : ℝ) * ((-a^2 - b^2 + 5)) * (1)^2 := by positivity
  have hid : ( 13  ) - ( a * b + a + 5 * b ) = (11/2 : ℝ) * (1) * (-a/11 - 5*b/11 + 1)^2 + (16/11 : ℝ) * (1) * (a - b/2)^2 + (3/2 : ℝ) * ((-a^2 - b^2 + 5)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 5), a * b + a + 5 * b ≤ 13) := @solution
#print axioms solution

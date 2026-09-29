-- Prove2me | solution 1 for WorkbookSource.base_815
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:08.931984+00:00
-- url     : https://prove2.me/submissions/c166a223-75da-4b09-878d-55151d92ad58

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : a^2 + b^2 = a + b) : a + b - a * b ≤ 9 / 8  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (a^2 - a + b^2 - b) := by linarith only [hab]
  have hw3 : 0 ≤ (-a^2 + a - b^2 + b) := by linarith only [hab]
  have hsum : 0 ≤ (9/8 : ℝ) * (1) * (-2*a/3 - 2*b/3 + 1)^2 + (1/2 : ℝ) * ((-a^2 + a - b^2 + b)) * (1)^2 := by positivity
  have hid : ( 9 / 8  ) - ( a + b - a * b ) = (9/8 : ℝ) * (1) * (-2*a/3 - 2*b/3 + 1)^2 + (1/2 : ℝ) * ((-a^2 + a - b^2 + b)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hab : a^2 + b^2 = a + b), a + b - a * b ≤ 9 / 8) := @solution
#print axioms solution

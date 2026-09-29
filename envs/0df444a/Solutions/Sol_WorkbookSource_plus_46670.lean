-- Prove2me | solution 1 for WorkbookSource.plus_46670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:26.991999+00:00
-- url     : https://prove2.me/submissions/6dbecdd2-ce97-4d54-b519-1003d61873ad

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a * b + b * c + c * a ≥ 3 * a * b * c   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a - b - c + 3) := by linarith only [hab]
  have hsum : 0 ≤ (1/9 : ℝ) * ((-a - b - c + 3)) * (a + b + c)^2 + (1/9 : ℝ) * ((a + b + c - 3)) * (-a/2 - b/2 + c)^2 + (1/12 : ℝ) * ((a + b + c - 3)) * (-a + b)^2 + (1/3 : ℝ) * ((c)) * (-a + b)^2 + (1/3 : ℝ) * ((b)) * (-a + c)^2 + (1/3 : ℝ) * ((a)) * (-b + c)^2 := by positivity
  have hid : ( a * b + b * c + c * a ) - ( 3 * a * b * c   ) = (1/9 : ℝ) * ((-a - b - c + 3)) * (a + b + c)^2 + (1/9 : ℝ) * ((a + b + c - 3)) * (-a/2 - b/2 + c)^2 + (1/12 : ℝ) * ((a + b + c - 3)) * (-a + b)^2 + (1/3 : ℝ) * ((c)) * (-a + b)^2 + (1/3 : ℝ) * ((b)) * (-a + c)^2 + (1/3 : ℝ) * ((a)) * (-b + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), a * b + b * c + c * a ≥ 3 * a * b * c) := @solution
#print axioms solution

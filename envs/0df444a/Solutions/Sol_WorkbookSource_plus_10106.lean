-- Prove2me | solution 1 for WorkbookSource.plus_10106
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:36.385982+00:00
-- url     : https://prove2.me/submissions/d6df6ea8-b6e2-4e6e-9e92-7e2602715df4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^3 + b^3 = 2) : a + b + (1 / 8) * (a^2 - b^2)^2 ≤ 2   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (a^3 + b^3 - 2) := by linarith only [hab]
  have hw3 : 0 ≤ (-a^3 - b^3 + 2) := by linarith only [hab]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a^2/12 - a*b/6 - a/3 - b^2/12 - b/3 + 1)^2 + (1/9 : ℝ) * (1) * (-a^2/2 - a*b + a - b^2/2 + b)^2 + (1/6 : ℝ) * ((b) * (-a^3 - b^3 + 2)) * (1)^2 + (1/6 : ℝ) * ((a) * (-a^3 - b^3 + 2)) * (1)^2 := by positivity
  have hid : ( 2   ) - ( a + b + (1 / 8) * (a^2 - b^2)^2 ) = (2 : ℝ) * (1) * (-a^2/12 - a*b/6 - a/3 - b^2/12 - b/3 + 1)^2 + (1/9 : ℝ) * (1) * (-a^2/2 - a*b + a - b^2/2 + b)^2 + (1/6 : ℝ) * ((b) * (-a^3 - b^3 + 2)) * (1)^2 + (1/6 : ℝ) * ((a) * (-a^3 - b^3 + 2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^3 + b^3 = 2), a + b + (1 / 8) * (a^2 - b^2)^2 ≤ 2) := @solution
#print axioms solution

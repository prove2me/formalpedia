-- Prove2me | solution 1 for WorkbookSource.plus_61196
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:29.711589+00:00
-- url     : https://prove2.me/submissions/887b29f2-75e0-4f88-8ca4-ac408af838e6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c s : ℝ} (hx: a + b + c = 2 * s) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (s - a) * (b - c) ^ 2 + (s - b) * (c - a) ^ 2 + (s - c) * (a - b) ^ 2 ≤ a * b * c   := by
  have hw0 : 0 ≤ (a + b + c - 2*s) := by linarith only [hx]
  have hw1 : 0 ≤ (-a - b - c + 2*s) := by linarith only [hx]
  have hw2 : 0 ≤ (a + b - c) := by linarith only [hab]
  have hw3 : 0 ≤ (-a + b + c) := by linarith only [hbc]
  have hw4 : 0 ≤ (a - b + c) := by linarith only [hca]
  have hsum : 0 ≤ (1 : ℝ) * ((a + b - c) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (a + b - c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (a + b - c) * (-a + b + c)) * (1)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (c)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (b)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (a)^2 := by positivity
  have hid : ( a * b * c   ) - ( (s - a) * (b - c) ^ 2 + (s - b) * (c - a) ^ 2 + (s - c) * (a - b) ^ 2 ) = (1 : ℝ) * ((a + b - c) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (a + b - c) * (a - b + c)) * (1)^2 + (1/2 : ℝ) * ((-a - b - c + 2*s) * (a + b - c) * (-a + b + c)) * (1)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (c)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (b)^2 + (1/2 : ℝ) * ((a + b + c - 2*s)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c s : ℝ} (hx: a + b + c = 2 * s) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b), (s - a) * (b - c) ^ 2 + (s - b) * (c - a) ^ 2 + (s - c) * (a - b) ^ 2 ≤ a * b * c) := @solution
#print axioms solution

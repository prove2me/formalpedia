-- Prove2me | solution 1 for WorkbookSource.base_11742
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:44.687063+00:00
-- url     : https://prove2.me/submissions/1651d3ed-26dd-4a0f-bf4f-7ce6e667ee4f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c : ℝ} (hx: a + b + c = 6) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * a * b * c + 72 ≥ 8 * (a * b + b * c + a * c)  := by
  have hw0 : 0 ≤ (a + b + c - 6) := by linarith only [hx]
  have hw1 : 0 ≤ (-a - b - c + 6) := by linarith only [hx]
  have hw2 : 0 ≤ (a + b - c) := by linarith only [hab]
  have hw3 : 0 ≤ (-a + b + c) := by linarith only [hbc]
  have hw4 : 0 ≤ (a - b + c) := by linarith only [hca]
  have hsum : 0 ≤ (1/6 : ℝ) * ((a - b + c)) * (-a + c)^2 + (1/6 : ℝ) * ((-a + b + c)) * (-b + c)^2 + (1/6 : ℝ) * ((a + b - c)) * (-a + b)^2 + (12 : ℝ) * ((-a - b - c + 6)) * (a/12 + b/12 + c/12 + 1)^2 + (1/60 : ℝ) * ((-a - b - c + 6)) * (a + b + c)^2 + (1/10 : ℝ) * ((a + b + c - 6)) * (a + b + c)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (a + b - c) * (a - b + c)) * (1)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (a + b - c) * (-a + b + c)) * (1)^2 := by positivity
  have hid : ( 3 * a * b * c + 72 ) - ( 8 * (a * b + b * c + a * c)  ) = (1/6 : ℝ) * ((a - b + c)) * (-a + c)^2 + (1/6 : ℝ) * ((-a + b + c)) * (-b + c)^2 + (1/6 : ℝ) * ((a + b - c)) * (-a + b)^2 + (12 : ℝ) * ((-a - b - c + 6)) * (a/12 + b/12 + c/12 + 1)^2 + (1/60 : ℝ) * ((-a - b - c + 6)) * (a + b + c)^2 + (1/10 : ℝ) * ((a + b + c - 6)) * (a + b + c)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (a + b - c) * (a - b + c)) * (1)^2 + (1/3 : ℝ) * ((a + b + c - 6) * (a + b - c) * (-a + b + c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ} (hx: a + b + c = 6) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b), 3 * a * b * c + 72 ≥ 8 * (a * b + b * c + a * c)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.plus_77465
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:33.543999+00:00
-- url     : https://prove2.me/submissions/e246315b-e273-440e-b884-95663153f063

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (hx: a + b + c = 3) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 13   := by
  have hw0 : 0 ≤ (a + b + c - 3) := by linarith only [hx]
  have hw1 : 0 ≤ (-a - b - c + 3) := by linarith only [hx]
  have hw2 : 0 ≤ (a + b - c) := by linarith only [hab]
  have hw3 : 0 ≤ (-a + b + c) := by linarith only [hbc]
  have hw4 : 0 ≤ (a - b + c) := by linarith only [hca]
  have hsum : 0 ≤ (20/9 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (5/3 : ℝ) * (1) * (-a + b)^2 + (1/18 : ℝ) * ((a - b + c)) * (-a + c)^2 + (1/18 : ℝ) * ((-a + b + c)) * (-b + c)^2 + (1/18 : ℝ) * ((a + b - c)) * (-a + b)^2 + (13/6 : ℝ) * ((a + b + c - 3)) * (a/3 + b/3 + c/3 + 1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (a + b - c) * (a - b + c)) * (1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (a + b - c) * (-a + b + c)) * (1)^2 + (13/18 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (a - b + c)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (-a + b + c)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (a + b - c)) * (1)^2 := by positivity
  have hid : ( 4 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ) - ( 13   ) = (20/9 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (5/3 : ℝ) * (1) * (-a + b)^2 + (1/18 : ℝ) * ((a - b + c)) * (-a + c)^2 + (1/18 : ℝ) * ((-a + b + c)) * (-b + c)^2 + (1/18 : ℝ) * ((a + b - c)) * (-a + b)^2 + (13/6 : ℝ) * ((a + b + c - 3)) * (a/3 + b/3 + c/3 + 1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (-a + b + c) * (a - b + c)) * (1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (a + b - c) * (a - b + c)) * (1)^2 + (1/9 : ℝ) * ((a + b + c - 3) * (a + b - c) * (-a + b + c)) * (1)^2 + (13/18 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (a - b + c)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (-a + b + c)) * (1)^2 + (13/54 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3) * (a + b - c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (hx: a + b + c = 3) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b), 4 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 13) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_4633
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:27.296011+00:00
-- url     : https://prove2.me/submissions/d46ceb25-e2c4-4e53-865e-8ea9371532d6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = a^2 + b^2 + c^2) : a * b + b * c + c * a ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a^2 + a - b^2 + b - c^2 + c) := by linarith only [hab]
  have hw4 : 0 ≤ (a^2 - a + b^2 - b + c^2 - c) := by linarith only [hab]
  have hsum : 0 ≤ (1/3 : ℝ) * (1) * (a^2/2 - a/2 + b^2/2 - b/2 - c^2 + c)^2 + (1/4 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 + (9/8 : ℝ) * ((a^2 - a + b^2 - b + c^2 - c)) * (-a/3 - b/3 - c/3 + 1)^2 + (1/8 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c)) * (a + b + c + 1)^2 + (1/3 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c) * (a^2 - a + b^2 - b + c^2 - c)) * (1)^2 + (1 : ℝ) * ((c)) * (1 - c)^2 + (1 : ℝ) * ((b)) * (1 - b)^2 + (1 : ℝ) * ((a)) * (1 - a)^2 := by positivity
  have hid : ( a * b + b * c + c * a ) - ( a^2 * b^2 + b^2 * c^2 + c^2 * a^2  ) = (1/3 : ℝ) * (1) * (a^2/2 - a/2 + b^2/2 - b/2 - c^2 + c)^2 + (1/4 : ℝ) * (1) * (a^2 - a - b^2 + b)^2 + (9/8 : ℝ) * ((a^2 - a + b^2 - b + c^2 - c)) * (-a/3 - b/3 - c/3 + 1)^2 + (1/8 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c)) * (a + b + c + 1)^2 + (1/3 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c) * (a^2 - a + b^2 - b + c^2 - c)) * (1)^2 + (1 : ℝ) * ((c)) * (1 - c)^2 + (1 : ℝ) * ((b)) * (1 - b)^2 + (1 : ℝ) * ((a)) * (1 - a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b + c = a^2 + b^2 + c^2), a * b + b * c + c * a ≥ a^2 * b^2 + b^2 * c^2 + c^2 * a^2) := @solution
#print axioms solution

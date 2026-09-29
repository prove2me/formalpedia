-- Prove2me | solution 1 for WorkbookSource.plus_31335
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:39.688403+00:00
-- url     : https://prove2.me/submissions/09d1b07d-cfa9-4119-880a-1903fbfbbc44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : 2 * (a + b + c) ≥ 3 + 3/8 * (a + b) * (b + c) * (c + a)   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 + b^2 + c^2 - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a^2 - b^2 - c^2 + 3) := by linarith only [hab]
  have hsum : 0 ≤ (1 : ℝ) * ((a^2 + b^2 + c^2 - 3)) * (1)^2 + (1/2 : ℝ) * ((c)) * (1 - c)^2 + (1/8 : ℝ) * ((c)) * (-a + b)^2 + (1/2 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/2 : ℝ) * ((b)) * (1 - b)^2 + (1/8 : ℝ) * ((b)) * (-a + c)^2 + (1/2 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/2 : ℝ) * ((a)) * (1 - a)^2 + (1/8 : ℝ) * ((a)) * (-b + c)^2 + (1/2 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by positivity
  have hid : ( 2 * (a + b + c) ) - ( 3 + 3/8 * (a + b) * (b + c) * (c + a)   ) = (1 : ℝ) * ((a^2 + b^2 + c^2 - 3)) * (1)^2 + (1/2 : ℝ) * ((c)) * (1 - c)^2 + (1/8 : ℝ) * ((c)) * (-a + b)^2 + (1/2 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/2 : ℝ) * ((b)) * (1 - b)^2 + (1/8 : ℝ) * ((b)) * (-a + c)^2 + (1/2 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/2 : ℝ) * ((a)) * (1 - a)^2 + (1/8 : ℝ) * ((a)) * (-b + c)^2 + (1/2 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3), 2 * (a + b + c) ≥ 3 + 3/8 * (a + b) * (b + c) * (c + a)) := @solution
#print axioms solution

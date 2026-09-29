-- Prove2me | solution 1 for WorkbookSource.plus_48969
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:27.691886+00:00
-- url     : https://prove2.me/submissions/959cec8b-1178-4b2a-b9e4-297dd5c9cee1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : 6 * a * b * c + 11 * (a + b + c) ≥ (a + b + c)^3 + 12   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 + b^2 + c^2 - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a^2 - b^2 - c^2 + 3) := by linarith only [hab]
  have hsum : 0 ≤ (4 : ℝ) * ((a^2 + b^2 + c^2 - 3)) * (1)^2 + (2 : ℝ) * ((c)) * (1 - c)^2 + (3 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (2 : ℝ) * ((b)) * (1 - b)^2 + (3 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (2 : ℝ) * ((a)) * (1 - a)^2 + (3 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by positivity
  have hid : ( 6 * a * b * c + 11 * (a + b + c) ) - ( (a + b + c)^3 + 12   ) = (4 : ℝ) * ((a^2 + b^2 + c^2 - 3)) * (1)^2 + (2 : ℝ) * ((c)) * (1 - c)^2 + (3 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (2 : ℝ) * ((b)) * (1 - b)^2 + (3 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (2 : ℝ) * ((a)) * (1 - a)^2 + (3 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3), 6 * a * b * c + 11 * (a + b + c) ≥ (a + b + c)^3 + 12) := @solution
#print axioms solution

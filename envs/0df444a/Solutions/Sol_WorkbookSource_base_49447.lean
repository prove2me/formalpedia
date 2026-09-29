-- Prove2me | solution 1 for WorkbookSource.base_49447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:32.979412+00:00
-- url     : https://prove2.me/submissions/c082decf-2faf-4503-9a37-9d439565264d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ 3 * (a + b + c)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 + b^2 + c^2 - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a^2 - b^2 - c^2 + 3) := by linarith only [hab]
  have hsum : 0 ≤ (1 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (1 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by positivity
  have hid : ( 3 * (a + b + c)  ) - ( a^3 + b^3 + c^3 + 6 * a * b * c ) = (1 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (1 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3), a^3 + b^3 + c^3 + 6 * a * b * c ≤ 3 * (a + b + c)) := @solution
#print axioms solution

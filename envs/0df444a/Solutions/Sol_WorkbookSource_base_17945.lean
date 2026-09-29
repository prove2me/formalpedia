-- Prove2me | solution 1 for WorkbookSource.base_17945
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:12.678385+00:00
-- url     : https://prove2.me/submissions/891da7f8-df05-4aba-836e-6ee9ba821eb7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : a^2 * b + b^2 * c + c^2 * a ≤ a + b + c  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 + b^2 + c^2 - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a^2 - b^2 - c^2 + 3) := by linarith only [hab]
  have hsum : 0 ≤ (1/3 : ℝ) * ((c)) * (-a + c)^2 + (1/3 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((b)) * (-b + c)^2 + (1/3 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((a)) * (-a + b)^2 + (1/3 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by positivity
  have hid : ( a + b + c  ) - ( a^2 * b + b^2 * c + c^2 * a ) = (1/3 : ℝ) * ((c)) * (-a + c)^2 + (1/3 : ℝ) * ((c) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((b)) * (-b + c)^2 + (1/3 : ℝ) * ((b) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 + (1/3 : ℝ) * ((a)) * (-a + b)^2 + (1/3 : ℝ) * ((a) * (-a^2 - b^2 - c^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3), a^2 * b + b^2 * c + c^2 * a ≤ a + b + c) := @solution
#print axioms solution

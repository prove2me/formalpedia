-- Prove2me | solution 1 for WorkbookSource.plus_30899
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:47:47.989098+00:00
-- url     : https://prove2.me/submissions/df4d8f60-d357-489e-8d66-3e3335b0d82b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = (5/2) * (a * b + b * c + c * a)) : 11 * (a^4 + b^4 + c^4) ≥ 17 * (a^3 * b + b^3 * c + c^3 * a) + 129 * a * b * c * (a + b + c)   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 - 5*a*b/2 - 5*a*c/2 + b^2 - 5*b*c/2 + c^2) := by linarith only [hab]
  have hw4 : 0 ≤ (-a^2 + 5*a*b/2 + 5*a*c/2 - b^2 + 5*b*c/2 - c^2) := by linarith only [hab]
  have hsum : 0 ≤ (323/9 : ℝ) * (1) * (7*a^2/38 - a*b/2 - a*c/2 - 4*b^2/19 + b*c + c^2/38)^2 + (323/12 : ℝ) * (1) * (3*a^2/19 - a*b + a*c + 2*b^2/19 - 5*c^2/19)^2 + (262/27 : ℝ) * ((a^2 - 5*a*b/2 - 5*a*c/2 + b^2 - 5*b*c/2 + c^2)) * (a + b + c)^2 + (16/27 : ℝ) * ((a^2 - 5*a*b/2 - 5*a*c/2 + b^2 - 5*b*c/2 + c^2) * (-a^2 + 5*a*b/2 + 5*a*c/2 - b^2 + 5*b*c/2 - c^2)) * (1)^2 := by positivity
  have hid : ( 11 * (a^4 + b^4 + c^4) ) - ( 17 * (a^3 * b + b^3 * c + c^3 * a) + 129 * a * b * c * (a + b + c)   ) = (323/9 : ℝ) * (1) * (7*a^2/38 - a*b/2 - a*c/2 - 4*b^2/19 + b*c + c^2/38)^2 + (323/12 : ℝ) * (1) * (3*a^2/19 - a*b + a*c + 2*b^2/19 - 5*c^2/19)^2 + (262/27 : ℝ) * ((a^2 - 5*a*b/2 - 5*a*c/2 + b^2 - 5*b*c/2 + c^2)) * (a + b + c)^2 + (16/27 : ℝ) * ((a^2 - 5*a*b/2 - 5*a*c/2 + b^2 - 5*b*c/2 + c^2) * (-a^2 + 5*a*b/2 + 5*a*c/2 - b^2 + 5*b*c/2 - c^2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = (5/2) * (a * b + b * c + c * a)), 11 * (a^4 + b^4 + c^4) ≥ 17 * (a^3 * b + b^3 * c + c^3 * a) + 129 * a * b * c * (a + b + c)) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_49027
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:56:44.686807+00:00
-- url     : https://prove2.me/submissions/d02e65ad-619c-46fb-8158-c7cfffad2680

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : a^3 + b^3 + c^3 ≤ 1 + 3 * a * b * c  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (1/2 : ℝ) * (1) * (a^2/10 + a*b + a*c/2 + a/2 + b^2/10 + b*c/2 + b/2 - 2*c^2/5 + c - 3/5)^2 + (3/8 : ℝ) * (1) * (a^2/15 + a*c + a/3 - 3*b^2/5 + b*c/3 + b + 2*c^2/5 - 2/5)^2 + (1/3 : ℝ) * (1) * (-7*a^2/10 + a + 3*b^2/10 + b*c + 3*c^2/10 - 3/10)^2 + (33/40 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (a/3 + b/3 + c/3 + 1)^2 + (1/30 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a/2 - b/2 + c)^2 + (1/40 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a + b)^2 + (1/40 : ℝ) * ((a^2 + b^2 + c^2 - 1)) * (-a - b - c + 1)^2 + (7/100 : ℝ) * ((a^2 + b^2 + c^2 - 1) * (-a^2 - b^2 - c^2 + 1)) * (1)^2 := by positivity
  have hid : ( 1 + 3 * a * b * c  ) - ( a^3 + b^3 + c^3 ) = (1/2 : ℝ) * (1) * (a^2/10 + a*b + a*c/2 + a/2 + b^2/10 + b*c/2 + b/2 - 2*c^2/5 + c - 3/5)^2 + (3/8 : ℝ) * (1) * (a^2/15 + a*c + a/3 - 3*b^2/5 + b*c/3 + b + 2*c^2/5 - 2/5)^2 + (1/3 : ℝ) * (1) * (-7*a^2/10 + a + 3*b^2/10 + b*c + 3*c^2/10 - 3/10)^2 + (33/40 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (a/3 + b/3 + c/3 + 1)^2 + (1/30 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a/2 - b/2 + c)^2 + (1/40 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a + b)^2 + (1/40 : ℝ) * ((a^2 + b^2 + c^2 - 1)) * (-a - b - c + 1)^2 + (7/100 : ℝ) * ((a^2 + b^2 + c^2 - 1) * (-a^2 - b^2 - c^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1), a^3 + b^3 + c^3 ≤ 1 + 3 * a * b * c) := @solution
#print axioms solution

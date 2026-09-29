-- Prove2me | solution 1 for WorkbookCorrected.base_44343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:00:11.240015+00:00
-- url     : https://prove2.me/submissions/43eb3ae0-fcbc-4b1e-a3a3-61664e063c59

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1) :  a^2 * b * (b^3 - 1) + b^2 * c * (c^3 - 1) + c^2 * a * (a^3 - 1) ≥ 0  := by
  have hw0 : 0 ≤ (a*b*c - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a*b*c + 1) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2*c/2 - a*b^2/2 + b*c^2)^2 + (3/4 : ℝ) * (1) * (-a^2*c + a*b^2)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a*c/4 - 3*b^2/4 + c)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a^2/4 - 3*b*c/4 + b)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a*b/4 + a - 3*c^2/4)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a*b + c^2)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a^2 + b*c)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a*c + b^2)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a*c/4 + 3*b^2/4 + c)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a^2/4 + 3*b*c/4 + b)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a*b/4 + a + 3*c^2/4)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a*b + c^2)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a^2 + b*c)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a*c + b^2)^2 := by positivity
  have hid : (  a^2 * b * (b^3 - 1) + b^2 * c * (c^3 - 1) + c^2 * a * (a^3 - 1) ) - ( 0  ) = (1 : ℝ) * (1) * (-a^2*c/2 - a*b^2/2 + b*c^2)^2 + (3/4 : ℝ) * (1) * (-a^2*c + a*b^2)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a*c/4 - 3*b^2/4 + c)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a^2/4 - 3*b*c/4 + b)^2 + (1/6 : ℝ) * ((-a*b*c + 1)) * (-3*a*b/4 + a - 3*c^2/4)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a*b + c^2)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a^2 + b*c)^2 + (1/160 : ℝ) * ((-a*b*c + 1)) * (a*c + b^2)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a*c/4 + 3*b^2/4 + c)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a^2/4 + 3*b*c/4 + b)^2 + (1/6 : ℝ) * ((a*b*c - 1)) * (3*a*b/4 + a + 3*c^2/4)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a*b + c^2)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a^2 + b*c)^2 + (1/160 : ℝ) * ((a*b*c - 1)) * (a*c + b^2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a * b * c = 1), a^2 * b * (b^3 - 1) + b^2 * c * (c^3 - 1) + c^2 * a * (a^3 - 1) ≥ 0) := @solution
#print axioms solution

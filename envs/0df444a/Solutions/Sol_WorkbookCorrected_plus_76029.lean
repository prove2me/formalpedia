-- Prove2me | solution 1 for WorkbookCorrected.plus_76029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:07.261847+00:00
-- url     : https://prove2.me/submissions/e22b30a9-e038-4048-b578-66d693e40096

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h : a * b * c = 1) :
  (a * b - 1) ^ 2 + (b * c - 1) ^ 2 + (c * a - 1) ^ 2 + (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 ≥ a * b * (a - b) + b * c * (b - c) + c * a * (c - a)   := by
  have hw0 : 0 ≤ (a*b*c - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a*b*c + 1) := by linarith only [h]
  have hsum : 0 ≤ (6 : ℝ) * (1) * (-a*b/6 - a*c/6 - a/6 - b*c/6 - b/6 - c/6 + 1)^2 + (5/6 : ℝ) * (1) * (-a*b/5 - 4*a*c/5 - a/5 + 2*b*c/5 - b/5 + c)^2 + (4/5 : ℝ) * (1) * (3*a*b/8 - 3*a*c/8 - a/4 - 3*b*c/4 + b)^2 + (3/4 : ℝ) * (1) * (-5*a*b/6 + a*c/6 + a - b*c/3)^2 + (1/6 : ℝ) * (1) * (-a*b/2 - a*c/2 + b*c)^2 + (1/8 : ℝ) * (1) * (-a*b + a*c)^2 := by positivity
  have hid : (
  (a * b - 1) ^ 2 + (b * c - 1) ^ 2 + (c * a - 1) ^ 2 + (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 ) - ( a * b * (a - b) + b * c * (b - c) + c * a * (c - a)   ) = (6 : ℝ) * (1) * (-a*b/6 - a*c/6 - a/6 - b*c/6 - b/6 - c/6 + 1)^2 + (5/6 : ℝ) * (1) * (-a*b/5 - 4*a*c/5 - a/5 + 2*b*c/5 - b/5 + c)^2 + (4/5 : ℝ) * (1) * (3*a*b/8 - 3*a*c/8 - a/4 - 3*b*c/4 + b)^2 + (3/4 : ℝ) * (1) * (-5*a*b/6 + a*c/6 + a - b*c/3)^2 + (1/6 : ℝ) * (1) * (-a*b/2 - a*c/2 + b*c)^2 + (1/8 : ℝ) * (1) * (-a*b + a*c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h : a * b * c = 1), (a * b - 1) ^ 2 + (b * c - 1) ^ 2 + (c * a - 1) ^ 2 + (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 ≥ a * b * (a - b) + b * c * (b - c) + c * a * (c - a)) := @solution
#print axioms solution

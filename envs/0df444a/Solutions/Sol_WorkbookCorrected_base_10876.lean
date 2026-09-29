-- Prove2me | solution 1 for WorkbookCorrected.base_10876
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:51.037307+00:00
-- url     : https://prove2.me/submissions/a8342ec8-dd6f-4a24-aa79-2f76c07ff59f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (source_domain_d : 0 < d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 11 * a * b * c * (a + b + c)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 + (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 + (5 : ℝ) * ((b) * (c)) * (-b + c)^2 + (5 : ℝ) * ((a) * (c)) * (-a + c)^2 + (5 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( (a + b + c) ^ 4 ) - ( 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 11 * a * b * c * (a + b + c)  ) = (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 + (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 + (5 : ℝ) * ((b) * (c)) * (-b + c)^2 + (5 : ℝ) * ((a) * (c)) * (-a + c)^2 + (5 : ℝ) * ((a) * (b)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (source_domain_d : 0 < d) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + b + c) ^ 4 ≥ 16 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 11 * a * b * c * (a + b + c)) := @solution
#print axioms solution

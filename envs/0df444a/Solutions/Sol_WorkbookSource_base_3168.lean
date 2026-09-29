-- Prove2me | solution 1 for WorkbookSource.base_3168
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:43:29.110885+00:00
-- url     : https://prove2.me/submissions/4943649c-ae84-4737-9ccf-1b5d3dcf3bd1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d e : ℝ) (h : a * b + b * c + c * a = 20 * d * e) :
  13 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 3 * (a + b + c + d + e) ^ 2  := by
  have hw0 : 0 ≤ (a*b + a*c + b*c - 20*d*e) := by linarith only [h]
  have hw1 : 0 ≤ (-a*b - a*c - b*c + 20*d*e) := by linarith only [h]
  have hsum : 0 ≤ (10 : ℝ) * (1) * (-3*a/10 - 3*b/10 - 3*c/10 + d + e)^2 + (91/10 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (273/40 : ℝ) * (1) * (-a + b)^2 + (13/10 : ℝ) * ((a*b + a*c + b*c - 20*d*e)) * (1)^2 := by positivity
  have hid : (
  13 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ) - ( 3 * (a + b + c + d + e) ^ 2  ) = (10 : ℝ) * (1) * (-3*a/10 - 3*b/10 - 3*c/10 + d + e)^2 + (91/10 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (273/40 : ℝ) * (1) * (-a + b)^2 + (13/10 : ℝ) * ((a*b + a*c + b*c - 20*d*e)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d e : ℝ) (h : a * b + b * c + c * a = 20 * d * e), 13 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 3 * (a + b + c + d + e) ^ 2) := @solution
#print axioms solution

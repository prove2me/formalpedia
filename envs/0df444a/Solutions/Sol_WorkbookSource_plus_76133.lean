-- Prove2me | solution 1 for WorkbookSource.plus_76133
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:33.620889+00:00
-- url     : https://prove2.me/submissions/1972bf06-0965-40c7-9caf-b5dacce46fec

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : (a + b + c - 3 * a * b * c) ^ 2 + (a * b + b * c + c * a - 3) ^ 2 ≥ 8 * (a * b * c - 1) ^ 2   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (a*b*c - a*b/3 - a*c/3 - a/3 - b*c/3 - b/3 - c/3 + 1)^2 + (8/9 : ℝ) * (1) * (a*b - a*c/2 - a/2 - b*c/2 - b/2 + c)^2 + (2/3 : ℝ) * (1) * (a*c - a - b*c + b)^2 + (2/3 : ℝ) * ((c)) * (a*b - a - b + 1)^2 + (2/3 : ℝ) * ((b)) * (a*c - a - c + 1)^2 + (2/3 : ℝ) * ((a)) * (b*c - b - c + 1)^2 := by positivity
  have hid : ( (a + b + c - 3 * a * b * c) ^ 2 + (a * b + b * c + c * a - 3) ^ 2 ) - ( 8 * (a * b * c - 1) ^ 2   ) = (1 : ℝ) * (1) * (a*b*c - a*b/3 - a*c/3 - a/3 - b*c/3 - b/3 - c/3 + 1)^2 + (8/9 : ℝ) * (1) * (a*b - a*c/2 - a/2 - b*c/2 - b/2 + c)^2 + (2/3 : ℝ) * (1) * (a*c - a - b*c + b)^2 + (2/3 : ℝ) * ((c)) * (a*b - a - b + 1)^2 + (2/3 : ℝ) * ((b)) * (a*c - a - c + 1)^2 + (2/3 : ℝ) * ((a)) * (b*c - b - c + 1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), (a + b + c - 3 * a * b * c) ^ 2 + (a * b + b * c + c * a - 3) ^ 2 ≥ 8 * (a * b * c - 1) ^ 2) := @solution
#print axioms solution

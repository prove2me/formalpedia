-- Prove2me | solution 1 for WorkbookSource.base_316
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:31.758319+00:00
-- url     : https://prove2.me/submissions/0a41b9b8-24b2-466b-a091-5f6382c1e981

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a + b + c + 2 = a * b * c) :  (a - 1) * (b - 1) * (c - 1) * (a * b + b * c + c * a - 1) ≤ 11  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a*b*c + a + b + c + 2) := by linarith only [habc]
  have hw4 : 0 ≤ (a*b*c - a - b - c - 2) := by linarith only [habc]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a*c/2 + a/2 - b*c/2 + b/2 + c)^2 + (3/2 : ℝ) * (1) * (-2*a*b/3 + a*c/3 + a/3 - b*c/3 + b)^2 + (4/3 : ℝ) * (1) * (-a*b/2 - a*c/2 + a + b*c/2)^2 + (1/3 : ℝ) * ((a*b*c - a - b - c - 2)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((a*b*c - a - b - c - 2)) * (-a + b)^2 + (5 : ℝ) * ((-a*b*c + a + b + c + 2)) * (-a/5 - b/5 - c/5 + 1)^2 + (2/15 : ℝ) * ((-a*b*c + a + b + c + 2)) * (a + b + c)^2 := by positivity
  have hid : ( 11  ) - (  (a - 1) * (b - 1) * (c - 1) * (a * b + b * c + c * a - 1) ) = (2 : ℝ) * (1) * (-a*c/2 + a/2 - b*c/2 + b/2 + c)^2 + (3/2 : ℝ) * (1) * (-2*a*b/3 + a*c/3 + a/3 - b*c/3 + b)^2 + (4/3 : ℝ) * (1) * (-a*b/2 - a*c/2 + a + b*c/2)^2 + (1/3 : ℝ) * ((a*b*c - a - b - c - 2)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((a*b*c - a - b - c - 2)) * (-a + b)^2 + (5 : ℝ) * ((-a*b*c + a + b + c + 2)) * (-a/5 - b/5 - c/5 + 1)^2 + (2/15 : ℝ) * ((-a*b*c + a + b + c + 2)) * (a + b + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a + b + c + 2 = a * b * c), (a - 1) * (b - 1) * (c - 1) * (a * b + b * c + c * a - 1) ≤ 11) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_3158
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:37.163408+00:00
-- url     : https://prove2.me/submissions/f1ab580e-7f05-4f21-8280-87b87ffeea01

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c + a * b + b * c + c * a = 6) : 4 * (a + b + c) + a * b * c ≥ 13  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + a + b*c + b + c - 6) := by linarith only [habc]
  have hw4 : 0 ≤ (-a*b - a*c - a - b*c - b - c + 6) := by linarith only [habc]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (8/3 : ℝ) * ((a*b + a*c + a + b*c + b + c - 6)) * (1)^2 + (4/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 + (4/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 + (4/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 := by positivity
  have hid : ( 4 * (a + b + c) + a * b * c ) - ( 13  ) = (3 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (8/3 : ℝ) * ((a*b + a*c + a + b*c + b + c - 6)) * (1)^2 + (4/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 + (4/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 + (4/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - a - b*c - b - c + 6)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c + a * b + b * c + c * a = 6), 4 * (a + b + c) + a * b * c ≥ 13) := @solution
#print axioms solution

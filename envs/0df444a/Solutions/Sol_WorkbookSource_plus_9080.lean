-- Prove2me | solution 1 for WorkbookSource.plus_9080
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:24.928602+00:00
-- url     : https://prove2.me/submissions/86a8e8ba-85fe-41ce-b5a4-2fd70e03cc8e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1) :  (a - c) ^ 2 + (b - d) ^ 2 + 2 * a * d + 2 * b * c ≥ 1   := by
  have hw0 : 0 ≤ (a*b - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a*b + 1) := by linarith only [h]
  have hw2 : 0 ≤ (c^2 + d^2 - 1) := by linarith only [h']
  have hw3 : 0 ≤ (-c^2 - d^2 + 1) := by linarith only [h']
  have hsum : 0 ≤ (2 : ℝ) * (1) * (a/2 - b/2 + d)^2 + (2 : ℝ) * (1) * (-a/2 + b/2 + c)^2 + (1 : ℝ) * ((-c^2 - d^2 + 1)) * (1)^2 + (2 : ℝ) * ((a*b - 1)) * (1)^2 := by positivity
  have hid : (  (a - c) ^ 2 + (b - d) ^ 2 + 2 * a * d + 2 * b * c ) - ( 1   ) = (2 : ℝ) * (1) * (a/2 - b/2 + d)^2 + (2 : ℝ) * (1) * (-a/2 + b/2 + c)^2 + (1 : ℝ) * ((-c^2 - d^2 + 1)) * (1)^2 + (2 : ℝ) * ((a*b - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1), (a - c) ^ 2 + (b - d) ^ 2 + 2 * a * d + 2 * b * c ≥ 1) := @solution
#print axioms solution

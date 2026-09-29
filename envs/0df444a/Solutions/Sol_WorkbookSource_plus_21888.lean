-- Prove2me | solution 1 for WorkbookSource.plus_21888
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:38.450448+00:00
-- url     : https://prove2.me/submissions/f35dde5e-6279-4d6f-8080-ee1e0e9fa1c0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1) : (a - c) ^ 2 + (b - d) ^ 2 + a * d + b * c ≥ 27 / 20   := by
  have hw0 : 0 ≤ (a*b - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a*b + 1) := by linarith only [h]
  have hw2 : 0 ≤ (c^2 + d^2 - 1) := by linarith only [h']
  have hw3 : 0 ≤ (-c^2 - d^2 + 1) := by linarith only [h']
  have hsum : 0 ≤ (5/4 : ℝ) * (1) * (2*a/5 - 4*b/5 + d)^2 + (5/4 : ℝ) * (1) * (-4*a/5 + 2*b/5 + c)^2 + (1/4 : ℝ) * ((-c^2 - d^2 + 1)) * (1)^2 + (8/5 : ℝ) * ((a*b - 1)) * (1)^2 := by positivity
  have hid : ( (a - c) ^ 2 + (b - d) ^ 2 + a * d + b * c ) - ( 27 / 20   ) = (5/4 : ℝ) * (1) * (2*a/5 - 4*b/5 + d)^2 + (5/4 : ℝ) * (1) * (-4*a/5 + 2*b/5 + c)^2 + (1/4 : ℝ) * ((-c^2 - d^2 + 1)) * (1)^2 + (8/5 : ℝ) * ((a*b - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1), (a - c) ^ 2 + (b - d) ^ 2 + a * d + b * c ≥ 27 / 20) := @solution
#print axioms solution

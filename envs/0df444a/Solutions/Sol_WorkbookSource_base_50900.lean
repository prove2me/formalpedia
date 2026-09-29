-- Prove2me | solution 1 for WorkbookSource.base_50900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:40:58.044783+00:00
-- url     : https://prove2.me/submissions/94f8a7b0-e919-472b-9bfe-1671494d1b04

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z ≥ x^2 + y^3 + z^3) : 3 * x^2 + 4 * y^3 + 4 * z^3 ≤ 11  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (-x^2 + x - y^3 + y - z^3 + z) := by linarith only [h]
  have hsum : 0 ≤ (11 : ℝ) * (1) * (-3*x/11 - 4*y/11 - 4*z/11 + 1)^2 + (24/11 : ℝ) * (1) * (x - y/2 - z/2)^2 + (6 : ℝ) * ((-x^2 + x - y^3 + y - z^3 + z)) * (1)^2 + (2 : ℝ) * ((z)) * (-y/2 - z/2 + 1)^2 + (3/2 : ℝ) * ((z)) * (-y + z)^2 + (2 : ℝ) * ((y)) * (-y/2 - z/2 + 1)^2 + (3/2 : ℝ) * ((y)) * (-y + z)^2 := by positivity
  have hid : ( 11  ) - ( 3 * x^2 + 4 * y^3 + 4 * z^3 ) = (11 : ℝ) * (1) * (-3*x/11 - 4*y/11 - 4*z/11 + 1)^2 + (24/11 : ℝ) * (1) * (x - y/2 - z/2)^2 + (6 : ℝ) * ((-x^2 + x - y^3 + y - z^3 + z)) * (1)^2 + (2 : ℝ) * ((z)) * (-y/2 - z/2 + 1)^2 + (3/2 : ℝ) * ((z)) * (-y + z)^2 + (2 : ℝ) * ((y)) * (-y/2 - z/2 + 1)^2 + (3/2 : ℝ) * ((y)) * (-y + z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z ≥ x^2 + y^3 + z^3), 3 * x^2 + 4 * y^3 + 4 * z^3 ≤ 11) := @solution
#print axioms solution

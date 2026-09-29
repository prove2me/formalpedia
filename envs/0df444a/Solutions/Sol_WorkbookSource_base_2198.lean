-- Prove2me | solution 1 for WorkbookSource.base_2198
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:45.819978+00:00
-- url     : https://prove2.me/submissions/9c8a60be-2ab5-4bb6-a50a-76d1f2d0c82a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ 2) :  x^2 + y^3 ≤ x^3 + y^4 + 1753 / 6912  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (-x^3 - y^3 + 2) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (y^2 - y/2 - 3/16)^2 + (1/3 : ℝ) * (1) * (x - 2/3)^2 + (1/8 : ℝ) * (1) * (y - 3/4)^2 + (1 : ℝ) * ((x)) * (x - 2/3)^2 := by positivity
  have hid : ( x^3 + y^4 + 1753 / 6912  ) - (  x^2 + y^3 ) = (1 : ℝ) * (1) * (y^2 - y/2 - 3/16)^2 + (1/3 : ℝ) * (1) * (x - 2/3)^2 + (1/8 : ℝ) * (1) * (y - 3/4)^2 + (1 : ℝ) * ((x)) * (x - 2/3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x^3 + y^3 ≤ 2), x^2 + y^3 ≤ x^3 + y^4 + 1753 / 6912) := @solution
#print axioms solution

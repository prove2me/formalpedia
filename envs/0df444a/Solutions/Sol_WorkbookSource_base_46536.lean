-- Prove2me | solution 1 for WorkbookSource.base_46536
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:39:45.872945+00:00
-- url     : https://prove2.me/submissions/ccb5b87b-3030-4cd6-87c6-67f42d9930e3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z p q : ℝ) (hp : p = x + y + z) (hq : q = x*y + y*z + x*z) (h : p^2 - 2*q = 3) : 21*q ≤ 48 + (5 * p^2 * (2*q - 3)) / 9  := by
  have helim0 : p = (x + y + z) := by
    have hh := hp
    linarith only [hh]
  have helim1 : q = (x*y + x*z + y*z) := by
    have hh := hq
    try simp only [helim0] at hh
    linarith only [hh]
  have hw0 : 0 ≤ (x^2 + y^2 + z^2 - 3) := by
    have hh := h
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-x^2 - y^2 - z^2 + 3) := by
    have hh := h
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hsum : 0 ≤ (318/25 : ℝ) * (1) * (2*x^2/9 - 5*x*y/9 - 5*x*z/9 + 2*y^2/9 - 5*y*z/9 + 2*z^2/9 + 1)^2 + (23/27 : ℝ) * (1) * (-x^2/2 - x*y + x*z/2 - y^2/2 + y*z/2 + z^2)^2 + (23/36 : ℝ) * (1) * (-x^2 - x*z + y^2 + y*z)^2 + (294/25 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (1)^2 + (53/25 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (-x/2 - y/2 + z)^2 + (159/100 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (-x + y)^2 + (16/25 : ℝ) * ((x^2 + y^2 + z^2 - 3)) * (x + y + z)^2 := by positivity
  have hid : ( 48 + (5 * p^2 * (2*q - 3)) / 9  ) - ( 21*q ) = (318/25 : ℝ) * (1) * (2*x^2/9 - 5*x*y/9 - 5*x*z/9 + 2*y^2/9 - 5*y*z/9 + 2*z^2/9 + 1)^2 + (23/27 : ℝ) * (1) * (-x^2/2 - x*y + x*z/2 - y^2/2 + y*z/2 + z^2)^2 + (23/36 : ℝ) * (1) * (-x^2 - x*z + y^2 + y*z)^2 + (294/25 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (1)^2 + (53/25 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (-x/2 - y/2 + z)^2 + (159/100 : ℝ) * ((-x^2 - y^2 - z^2 + 3)) * (-x + y)^2 + (16/25 : ℝ) * ((x^2 + y^2 + z^2 - 3)) * (x + y + z)^2 := by
    try simp only [helim0, helim1]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z p q : ℝ) (hp : p = x + y + z) (hq : q = x*y + y*z + x*z) (h : p^2 - 2*q = 3), 21*q ≤ 48 + (5 * p^2 * (2*q - 3)) / 9) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_38262
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:14.784979+00:00
-- url     : https://prove2.me/submissions/364530f6-fa8d-46bd-bd39-eabbc6dfa138

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 3) : 11 + x*y*z ≥ 4*(x*y + y*z + z*x)  := by
  have helim : z = (-x - y + 3) := by linarith only [h]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-x - y + 3) := by
    have hh := hz
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (7/2 : ℝ) * (1) * (-x/2 - y/2 + 1)^2 + (11/56 : ℝ) * (1) * (-x + y)^2 + (5/2 : ℝ) * ((-x - y + 3)) * (-x/2 - y/2 + 1)^2 + (5/56 : ℝ) * ((-x - y + 3)) * (-x + y)^2 + (3/2 : ℝ) * ((y)) * (-3*x/7 - 4*y/7 + 1)^2 + (11/49 : ℝ) * ((y)) * (-x + y)^2 + (3/2 : ℝ) * ((x)) * (-4*x/7 - 3*y/7 + 1)^2 + (11/49 : ℝ) * ((x)) * (-x + y)^2 := by positivity
  have hid : ( 11 + x*y*z ) - ( 4*(x*y + y*z + z*x)  ) = (7/2 : ℝ) * (1) * (-x/2 - y/2 + 1)^2 + (11/56 : ℝ) * (1) * (-x + y)^2 + (5/2 : ℝ) * ((-x - y + 3)) * (-x/2 - y/2 + 1)^2 + (5/56 : ℝ) * ((-x - y + 3)) * (-x + y)^2 + (3/2 : ℝ) * ((y)) * (-3*x/7 - 4*y/7 + 1)^2 + (11/49 : ℝ) * ((y)) * (-x + y)^2 + (3/2 : ℝ) * ((x)) * (-4*x/7 - 3*y/7 + 1)^2 + (11/49 : ℝ) * ((x)) * (-x + y)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 3), 11 + x*y*z ≥ 4*(x*y + y*z + z*x)) := @solution
#print axioms solution

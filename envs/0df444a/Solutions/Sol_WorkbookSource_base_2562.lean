-- Prove2me | solution 1 for WorkbookSource.base_2562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:21.970777+00:00
-- url     : https://prove2.me/submissions/5ae1feec-e7e1-4b0f-a282-4d97733bca3e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 3) : x ^ 2 + y ^ 2 + z ^ 2 + 3 * x * y * z ≥ 9 / 2  := by
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
  have hsum : 0 ≤ (3/2 : ℝ) * ((-x - y + 3)) * (-2*x/3 - 2*y/3 + 1)^2 + (3/2 : ℝ) * ((y)) * (1 - 2*y/3)^2 + (3/2 : ℝ) * ((x)) * (1 - 2*x/3)^2 + (1 : ℝ) * ((x) * (y) * (-x - y + 3)) * (1)^2 := by positivity
  have hid : ( x ^ 2 + y ^ 2 + z ^ 2 + 3 * x * y * z ) - ( 9 / 2  ) = (3/2 : ℝ) * ((-x - y + 3)) * (-2*x/3 - 2*y/3 + 1)^2 + (3/2 : ℝ) * ((y)) * (1 - 2*y/3)^2 + (3/2 : ℝ) * ((x)) * (1 - 2*x/3)^2 + (1 : ℝ) * ((x) * (y) * (-x - y + 3)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z = 3), x ^ 2 + y ^ 2 + z ^ 2 + 3 * x * y * z ≥ 9 / 2) := @solution
#print axioms solution

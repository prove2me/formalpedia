-- Prove2me | solution 1 for WorkbookSource.base_19984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:12.690201+00:00
-- url     : https://prove2.me/submissions/78a2f633-7969-4e7e-ad38-cf2a9b5cf10e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3  := by
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
  have hsum : 0 ≤ (123/10 : ℝ) * (1) * (-x/2 - y/2 + 1)^2 + (17/40 : ℝ) * (1) * (-x + y)^2 + (99/10 : ℝ) * ((-x - y + 3)) * (-x/2 - y/2 + 1)^2 + (1/8 : ℝ) * ((-x - y + 3)) * (-x + y)^2 + (39/10 : ℝ) * ((y)) * (-x/3 - 2*y/3 + 1)^2 + (13/15 : ℝ) * ((y)) * (-x + y)^2 + (39/10 : ℝ) * ((x)) * (-2*x/3 - y/3 + 1)^2 + (13/15 : ℝ) * ((x)) * (-x + y)^2 := by positivity
  have hid : ( 2 * (x ^ 3 + y ^ 3 + z ^ 3) ) - ( x ^ 2 + y ^ 2 + z ^ 2 + 3  ) = (123/10 : ℝ) * (1) * (-x/2 - y/2 + 1)^2 + (17/40 : ℝ) * (1) * (-x + y)^2 + (99/10 : ℝ) * ((-x - y + 3)) * (-x/2 - y/2 + 1)^2 + (1/8 : ℝ) * ((-x - y + 3)) * (-x + y)^2 + (39/10 : ℝ) * ((y)) * (-x/3 - 2*y/3 + 1)^2 + (13/15 : ℝ) * ((y)) * (-x + y)^2 + (39/10 : ℝ) * ((x)) * (-2*x/3 - y/3 + 1)^2 + (13/15 : ℝ) * ((x)) * (-x + y)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3), 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 + y ^ 2 + z ^ 2 + 3) := @solution
#print axioms solution

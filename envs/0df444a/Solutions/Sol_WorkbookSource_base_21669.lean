-- Prove2me | solution 1 for WorkbookSource.base_21669
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:47.390765+00:00
-- url     : https://prove2.me/submissions/fab61e69-e8d3-4ca4-9a0d-da8d20456dc3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2) :  x * y + y * z + z * x ≤ (92 / 81 + 2 / 3 * x * y * z)  := by
  have helim : z = (-x - y + 2) := by linarith only [h]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-x - y + 2) := by
    have hh := hz
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (413/810 : ℝ) * (1) * (-3*x/4 - 3*y/4 + 1)^2 + (169/540 : ℝ) * ((-x - y + 2)) * (-3*x/4 - 3*y/4 + 1)^2 + (169/960 : ℝ) * ((y)) * (-7*x/13 + y - 4/13)^2 + (169/960 : ℝ) * ((x)) * (x - 7*y/13 - 4/13)^2 := by positivity
  have hid : ( (92 / 81 + 2 / 3 * x * y * z)  ) - (  x * y + y * z + z * x ) = (413/810 : ℝ) * (1) * (-3*x/4 - 3*y/4 + 1)^2 + (169/540 : ℝ) * ((-x - y + 2)) * (-3*x/4 - 3*y/4 + 1)^2 + (169/960 : ℝ) * ((y)) * (-7*x/13 + y - 4/13)^2 + (169/960 : ℝ) * ((x)) * (x - 7*y/13 - 4/13)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 2), x * y + y * z + z * x ≤ (92 / 81 + 2 / 3 * x * y * z)) := @solution
#print axioms solution

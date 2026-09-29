-- Prove2me | solution 1 for WorkbookSource.base_20770
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:13.289982+00:00
-- url     : https://prove2.me/submissions/94af3ea5-2775-40f7-b0d6-4ede33698c35

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 3 * x + 2 * y + z = 6) : x + x * y + x * y * z ≤ 3  := by
  have helim : z = (-3*x - 2*y + 6) := by linarith only [h]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-3*x - 2*y + 6) := by
    have hh := hz
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (61/30 : ℝ) * (1) * (-413*x/732 - 319*y/732 + 1)^2 + (31463/263520 : ℝ) * (1) * (-x + y)^2 + (4/15 : ℝ) * ((-3*x - 2*y + 6)) * (x - 31*y/48 - 17/48)^2 + (1103/8640 : ℝ) * ((-3*x - 2*y + 6)) * (1 - y)^2 + (521/180 : ℝ) * ((y)) * (-645*x/1042 - 397*y/1042 + 1)^2 + (1441/25008 : ℝ) * ((y)) * (-x + y)^2 + (131/45 : ℝ) * ((x)) * (-66*x/131 - 65*y/131 + 1)^2 + (8/131 : ℝ) * ((x)) * (-x + y)^2 := by positivity
  have hid : ( 3  ) - ( x + x * y + x * y * z ) = (61/30 : ℝ) * (1) * (-413*x/732 - 319*y/732 + 1)^2 + (31463/263520 : ℝ) * (1) * (-x + y)^2 + (4/15 : ℝ) * ((-3*x - 2*y + 6)) * (x - 31*y/48 - 17/48)^2 + (1103/8640 : ℝ) * ((-3*x - 2*y + 6)) * (1 - y)^2 + (521/180 : ℝ) * ((y)) * (-645*x/1042 - 397*y/1042 + 1)^2 + (1441/25008 : ℝ) * ((y)) * (-x + y)^2 + (131/45 : ℝ) * ((x)) * (-66*x/131 - 65*y/131 + 1)^2 + (8/131 : ℝ) * ((x)) * (-x + y)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : 3 * x + 2 * y + z = 6), x + x * y + x * y * z ≤ 3) := @solution
#print axioms solution

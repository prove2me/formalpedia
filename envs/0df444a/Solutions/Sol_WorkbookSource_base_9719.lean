-- Prove2me | solution 1 for WorkbookSource.base_9719
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:37:32.363264+00:00
-- url     : https://prove2.me/submissions/00577348-631b-458a-8e99-fabdf2d10be6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) (h : x + y + z + t = 1) : (1 - x) * (1 - y) * (1 - z) * (1 - t) ≤ 5 / 16 + x * y * z * t  := by
  have helim : t = (-x - y - z + 1) := by linarith only [h]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (z) := by
    have hh := hz
    try simp only [helim] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (-x - y - z + 1) := by
    have hh := ht
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1/3 : ℝ) * (1) * (x/2 + y/2 + z - 1/2)^2 + (1/4 : ℝ) * (1) * (x/3 + y - 1/3)^2 + (2/9 : ℝ) * (1) * (x - 1/4)^2 + (1/3 : ℝ) * ((-x - y - z + 1)) * (x + y + z - 3/4)^2 + (1/3 : ℝ) * ((z)) * (z - 1/4)^2 + (1/3 : ℝ) * ((y)) * (y - 1/4)^2 + (1/3 : ℝ) * ((x)) * (x - 1/4)^2 := by positivity
  have hid : ( 5 / 16 + x * y * z * t  ) - ( (1 - x) * (1 - y) * (1 - z) * (1 - t) ) = (1/3 : ℝ) * (1) * (x/2 + y/2 + z - 1/2)^2 + (1/4 : ℝ) * (1) * (x/3 + y - 1/3)^2 + (2/9 : ℝ) * (1) * (x - 1/4)^2 + (1/3 : ℝ) * ((-x - y - z + 1)) * (x + y + z - 3/4)^2 + (1/3 : ℝ) * ((z)) * (z - 1/4)^2 + (1/3 : ℝ) * ((y)) * (y - 1/4)^2 + (1/3 : ℝ) * ((x)) * (x - 1/4)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z t : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ht : 0 < t) (h : x + y + z + t = 1), (1 - x) * (1 - y) * (1 - z) * (1 - t) ≤ 5 / 16 + x * y * z * t) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_28066
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:14.092982+00:00
-- url     : https://prove2.me/submissions/8799d8e9-2238-42a4-a064-1bb09f5de3b8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 10  := by
  have helim : c = (-a - b + 3) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 3) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (17/3 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (13/36 : ℝ) * (1) * (-a + b)^2 + (34/9 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (1/6 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (25/9 : ℝ) * ((b)) * (-12*a/25 - 13*b/25 + 1)^2 + (9/25 : ℝ) * ((b)) * (-a + b)^2 + (25/9 : ℝ) * ((a)) * (-13*a/25 - 12*b/25 + 1)^2 + (9/25 : ℝ) * ((a)) * (-a + b)^2 := by positivity
  have hid : ( 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ) - ( 10  ) = (17/3 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (13/36 : ℝ) * (1) * (-a + b)^2 + (34/9 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (1/6 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (25/9 : ℝ) * ((b)) * (-12*a/25 - 13*b/25 + 1)^2 + (9/25 : ℝ) * ((b)) * (-a + b)^2 + (25/9 : ℝ) * ((a)) * (-13*a/25 - 12*b/25 + 1)^2 + (9/25 : ℝ) * ((a)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≥ 10) := @solution
#print axioms solution

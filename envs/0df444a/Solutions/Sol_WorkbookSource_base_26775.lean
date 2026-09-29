-- Prove2me | solution 1 for WorkbookSource.base_26775
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:09.717098+00:00
-- url     : https://prove2.me/submissions/2ba7da5b-462e-4a8d-a14e-2b5b5eab3ff1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) :  15 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a) + 9 * a * b * c ≥ 7  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 1) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (18 : ℝ) * ((-a - b + 1)) * (a + b - 2/3)^2 + (18 : ℝ) * ((b)) * (b - 1/3)^2 + (18 : ℝ) * ((a)) * (a - 1/3)^2 := by positivity
  have hid : (  15 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a) + 9 * a * b * c ) - ( 7  ) = (18 : ℝ) * ((-a - b + 1)) * (a + b - 2/3)^2 + (18 : ℝ) * ((b)) * (b - 1/3)^2 + (18 : ℝ) * ((a)) * (a - 1/3)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1), 15 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a) + 9 * a * b * c ≥ 7) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_18213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:12.004741+00:00
-- url     : https://prove2.me/submissions/82450c30-6129-4145-b148-83d7d5775602

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 3 * (a * b + b * c + c * a) * (1 + 48 * a * b * c) ≥ 75 * a * b * c  := by
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
  have hsum : 0 ≤ (48 : ℝ) * ((-a - b + 1)) * (-a^2 + 3*a/4 + b^2 - 3*b/4)^2 + (192 : ℝ) * ((b)) * (a*b - a/4 + b^2/2 - 5*b/8 + 1/8)^2 + (192 : ℝ) * ((a)) * (a^2/2 + a*b - 5*a/8 - b/4 + 1/8)^2 := by positivity
  have hid : ( 3 * (a * b + b * c + c * a) * (1 + 48 * a * b * c) ) - ( 75 * a * b * c  ) = (48 : ℝ) * ((-a - b + 1)) * (-a^2 + 3*a/4 + b^2 - 3*b/4)^2 + (192 : ℝ) * ((b)) * (a*b - a/4 + b^2/2 - 5*b/8 + 1/8)^2 + (192 : ℝ) * ((a)) * (a^2/2 + a*b - 5*a/8 - b/4 + 1/8)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), 3 * (a * b + b * c + c * a) * (1 + 48 * a * b * c) ≥ 75 * a * b * c) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_31850
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:11.145872+00:00
-- url     : https://prove2.me/submissions/1ae9715a-2320-4bf3-afe7-8320c4785dd0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≤ 27  := by
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
  have hsum : 0 ≤ (1/32 : ℝ) * ((-a - b + 3)) * (a + b)^2 + (49/32 : ℝ) * ((b)) * (a - b/7 + 3/7)^2 + (189/32 : ℝ) * ((b) * (-a - b + 3)) * (1)^2 + (49/32 : ℝ) * ((a)) * (-a/7 + b + 3/7)^2 + (189/32 : ℝ) * ((a) * (-a - b + 3)) * (1)^2 := by positivity
  have hid : ( 27  ) - ( 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ) = (1/32 : ℝ) * ((-a - b + 3)) * (a + b)^2 + (49/32 : ℝ) * ((b)) * (a - b/7 + 3/7)^2 + (189/32 : ℝ) * ((b) * (-a - b + 3)) * (1)^2 + (49/32 : ℝ) * ((a)) * (-a/7 + b + 3/7)^2 + (189/32 : ℝ) * ((a) * (-a - b + 3)) * (1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), 3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b * c ≤ 27) := @solution
#print axioms solution

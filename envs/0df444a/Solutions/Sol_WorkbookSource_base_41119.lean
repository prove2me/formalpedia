-- Prove2me | solution 1 for WorkbookSource.base_41119
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:50.379644+00:00
-- url     : https://prove2.me/submissions/d0740c27-ba19-4a3a-b7e6-638dfb0a8daf

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)(habc : a + b + c = 1) : a^2 + b^2 + c^2 ≤ 3 / 8 + a^4 + b^4 + c^4  := by
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
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a^2 - a*b + a - b^2 + b - 1/4)^2 + (1 : ℝ) * ((-a - b + 1)) * (a + b - 1/2)^2 + (1 : ℝ) * ((b)) * (b - 1/2)^2 + (1 : ℝ) * ((a)) * (a - 1/2)^2 + (1 : ℝ) * ((a) * (b) * (-a - b + 1)) * (1)^2 := by positivity
  have hid : ( 3 / 8 + a^4 + b^4 + c^4  ) - ( a^2 + b^2 + c^2 ) = (2 : ℝ) * (1) * (-a^2 - a*b + a - b^2 + b - 1/4)^2 + (1 : ℝ) * ((-a - b + 1)) * (a + b - 1/2)^2 + (1 : ℝ) * ((b)) * (b - 1/2)^2 + (1 : ℝ) * ((a)) * (a - 1/2)^2 + (1 : ℝ) * ((a) * (b) * (-a - b + 1)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)(habc : a + b + c = 1), a^2 + b^2 + c^2 ≤ 3 / 8 + a^4 + b^4 + c^4) := @solution
#print axioms solution

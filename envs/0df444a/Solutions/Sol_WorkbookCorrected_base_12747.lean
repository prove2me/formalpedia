-- Prove2me | solution 1 for WorkbookCorrected.base_12747
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:25.64806+00:00
-- url     : https://prove2.me/submissions/6d527845-506b-4576-b2eb-cb6133b8c8d0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 9) : x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ 108  := by
  have helim0 : z = (-x - y + 9) := by
    have hh := h
    linarith only [hh]
  have hw0 : 0 ≤ (x) := by
    have hh := hx
    try simp only [helim0] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (y) := by
    have hh := hy
    try simp only [helim0] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-x - y + 9) := by
    have hh := hz
    try simp only [helim0] at hh
    linarith only [hh]
  have hsum : 0 ≤ (12 : ℝ) * ((-x - y + 9)) * (-x/3 - y/6 + 1)^2 + (48 : ℝ) * ((y)) * (-x/12 - y/6 + 1)^2 + (3 : ℝ) * ((x)) * (-x/3 + y/3 + 1)^2 := by positivity
  have hid : ( 108  ) - ( x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ) = (12 : ℝ) * ((-x - y + 9)) * (-x/3 - y/6 + 1)^2 + (48 : ℝ) * ((y)) * (-x/12 - y/6 + 1)^2 + (3 : ℝ) * ((x)) * (-x/3 + y/3 + 1)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 9), x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ 108) ∧ (∃ x y z : ℝ, (0 ≤ x) ∧ (0 ≤ y) ∧ (0 ≤ z) ∧ (x + y + z = 9) ∧ ( x ^ 2 * y + y ^ 2 * z + z ^ 2 * x  =  108  )) := by
  constructor
  · exact p2mUpperBound
  · refine ⟨6, 3, 0, ?_⟩ <;> norm_num
example : ((∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 9), x ^ 2 * y + y ^ 2 * z + z ^ 2 * x ≤ 108) ∧ (∃ x y z : ℝ, (0 ≤ x) ∧ (0 ≤ y) ∧ (0 ≤ z) ∧ (x + y + z = 9) ∧ ( x ^ 2 * y + y ^ 2 * z + z ^ 2 * x  =  108  ))) := @solution
#print axioms solution

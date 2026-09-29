-- Prove2me | solution 1 for WorkbookCorrected.base_47199
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:27.435488+00:00
-- url     : https://prove2.me/submissions/0bffebfd-dfec-40f9-b241-f441c6e36508

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (x y z : ℝ) (h : x + y + z + 2 = x * y * z) : (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 4  := by
  have hw0 : 0 ≤ (-x*y*z + x + y + z + 2) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (x*y*z - x - y - z - 2) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-x*y*z + x*y + x*z + x + y*z + y + z + 1)^2 + (2 : ℝ) * ((x*y*z - x - y - z - 2)) * (1)^2 + (2/3 : ℝ) * ((x*y*z - x - y - z - 2)) * (x + y + z)^2 + (2/3 : ℝ) * ((-x*y*z + x + y + z + 2)) * (-x/2 - y/2 + z)^2 + (1/2 : ℝ) * ((-x*y*z + x + y + z + 2)) * (-x + y)^2 := by positivity
  have hid : ( (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ) - ( 4  ) = (1 : ℝ) * (1) * (-x*y*z + x*y + x*z + x + y*z + y + z + 1)^2 + (2 : ℝ) * ((x*y*z - x - y - z - 2)) * (1)^2 + (2/3 : ℝ) * ((x*y*z - x - y - z - 2)) * (x + y + z)^2 + (2/3 : ℝ) * ((-x*y*z + x + y + z + 2)) * (-x/2 - y/2 + z)^2 + (1/2 : ℝ) * ((-x*y*z + x + y + z + 2)) * (-x + y)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (x y z : ℝ) (h : x + y + z + 2 = x * y * z), (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 4) ∧ ((((0) : ℝ) + ((-1) : ℝ) + ((-1) : ℝ) + 2 = ((0) : ℝ) * ((-1) : ℝ) * ((-1) : ℝ)) ∧ ( (((0) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1)  =  4  )) := by
  constructor
  · exact p2mUpperBound
  · norm_num
example : ((∀ (x y z : ℝ) (h : x + y + z + 2 = x * y * z), (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 4) ∧ ((((0) : ℝ) + ((-1) : ℝ) + ((-1) : ℝ) + 2 = ((0) : ℝ) * ((-1) : ℝ) * ((-1) : ℝ)) ∧ ( (((0) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1) * (((-1) : ℝ) ^ 2 + 1)  =  4  ))) := @solution
#print axioms solution

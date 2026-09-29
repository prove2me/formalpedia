-- Prove2me | solution 1 for WorkbookSource.base_10868
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:06:46.878655+00:00
-- url     : https://prove2.me/submissions/1718992c-36c8-4d79-87de-492816f0e4c8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) : (3 * a + 4 * b) * (5 * a + 4) * (5 * b + 3) ≥ 0  := by
  have hw0 : 0 ≤ (a^2 + b^2 - 1) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a^2 - b^2 + 1) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (125/2 : ℝ) * (1) * (a*b + 3*a/5 + 4*b/5 + 12/25)^2 + (125/8 : ℝ) * (1) * (-a^2 + b^2 + 7/25)^2 + (125/8 : ℝ) * ((a^2 + b^2 - 1) * (-a^2 - b^2 + 1)) * (1)^2 := by positivity
  have hid : ( (3 * a + 4 * b) * (5 * a + 4) * (5 * b + 3) ) - ( 0  ) = (125/2 : ℝ) * (1) * (a*b + 3*a/5 + 4*b/5 + 12/25)^2 + (125/8 : ℝ) * (1) * (-a^2 + b^2 + 7/25)^2 + (125/8 : ℝ) * ((a^2 + b^2 - 1) * (-a^2 - b^2 + 1)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1), (3 * a + 4 * b) * (5 * a + 4) * (5 * b + 3) ≥ 0) := @solution
#print axioms solution

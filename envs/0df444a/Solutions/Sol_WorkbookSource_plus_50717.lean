-- Prove2me | solution 1 for WorkbookSource.plus_50717
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:16.518822+00:00
-- url     : https://prove2.me/submissions/a3c59eec-9c69-4be4-b94f-f3ced9dd9fef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d x : ℝ) (a2c2_leq_4b : a^2 + c^2 ≤ 4*b) : x^4 + a*x^3 + b*x^2 + c*x + 1 ≥ 0   := by
  have hw0 : 0 ≤ (-a^2 + 4*b - c^2) := by
    have hh := a2c2_leq_4b
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (c*x/2 + 1)^2 + (1 : ℝ) * (1) * (a*x/2 + x^2)^2 + (1/4 : ℝ) * ((-a^2 + 4*b - c^2)) * (x)^2 := by positivity
  have hid : ( x^4 + a*x^3 + b*x^2 + c*x + 1 ) - ( 0   ) = (1 : ℝ) * (1) * (c*x/2 + 1)^2 + (1 : ℝ) * (1) * (a*x/2 + x^2)^2 + (1/4 : ℝ) * ((-a^2 + 4*b - c^2)) * (x)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
example : (∀ (a b c d x : ℝ) (a2c2_leq_4b : a^2 + c^2 ≤ 4*b), x^4 + a*x^3 + b*x^2 + c*x + 1 ≥ 0) := @solution
#print axioms solution

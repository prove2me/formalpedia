-- Prove2me | solution 1 for WorkbookCorrected.base_49865
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:09.140976+00:00
-- url     : https://prove2.me/submissions/631af726-fbae-4ae4-9f86-1a1129ca8a7a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (h : a + b = 1) : 54 * a ^ 2 * b ^ 2 ≤ 4 * (a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2 + 1)  := by
  have helim0 : b = (1 - a) := by
    have hh := h
    linarith only [hh]
  have hsum : 0 ≤ (18 : ℝ) * (1) * (-2*a^3/3 + a^2 + a - 2/3)^2 := by positivity
  have hid : ( 4 * (a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2 + 1)  ) - ( 54 * a ^ 2 * b ^ 2 ) = (18 : ℝ) * (1) * (-2*a^3/3 + a^2 + a - 2/3)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (h : a + b = 1), 54 * a ^ 2 * b ^ 2 ≤ 4 * (a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2 + 1)) := @solution
#print axioms solution

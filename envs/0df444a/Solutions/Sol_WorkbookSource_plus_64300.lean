-- Prove2me | solution 1 for WorkbookSource.plus_64300
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:10:50.098836+00:00
-- url     : https://prove2.me/submissions/82dc1212-c3cb-453c-ab4d-25faf2595e47

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = 7) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + 30 * a * b * c + 15 ≥ 0   := by
  have helim0 : c = (-a - b + 7) := by
    have hh := h
    linarith only [hh]
  have hsum : 0 ≤ (65 : ℝ) * (1) * (-8*a^2*b/65 + a^2/65 - 8*a*b^2/65 + 57*a*b/65 - 7*a/65 + b^2/65 - 7*b/65 + 1)^2 + (3136/65 : ℝ) * (1) * (-a^2*b/56 - a^2/7 - a*b^2/56 - a*b/56 + a - b^2/7 + b)^2 := by positivity
  have hid : ( (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + 30 * a * b * c + 15 ) - ( 0   ) = (65 : ℝ) * (1) * (-8*a^2*b/65 + a^2/65 - 8*a*b^2/65 + 57*a*b/65 - 7*a/65 + b^2/65 - 7*b/65 + 1)^2 + (3136/65 : ℝ) * (1) * (-a^2*b/56 - a^2/7 - a*b^2/56 - a*b/56 + a - b^2/7 + b)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = 7), (a^2 + 1) * (b^2 + 1) * (c^2 + 1) + 30 * a * b * c + 15 ≥ 0) := @solution
#print axioms solution

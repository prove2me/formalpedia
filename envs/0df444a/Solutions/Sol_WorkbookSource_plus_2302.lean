-- Prove2me | solution 1 for WorkbookSource.plus_2302
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:06:48.080164+00:00
-- url     : https://prove2.me/submissions/9e6652b6-2287-4cf4-9816-bc3e42ea922d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h₁ : a^2 + b = 4) (h₂ : b^2 + c = 8) : 2 * a * b + b * c + c * a ≥ -32   := by
  have helim0 : b = (4 - a^2) := by
    have hh := h₁
    linarith only [hh]
  have helim1 : c = (-a^4 + 8*a^2 - 8) := by
    have hh := h₂
    try simp only [helim0] at hh
    linarith only [hh]
  have hsum : 0 ≤ (40 : ℝ) * (1) * (-1213*a^3/7920 + 3*a^2/40 + a)^2 + (96791/1568160 : ℝ) * (1) * (a^3 - 63558*a^2/96791)^2 + (8729/9582309 : ℝ) * (1) * (a^2)^2 := by positivity
  have hid : ( 2 * a * b + b * c + c * a ) - ( -32   ) = (40 : ℝ) * (1) * (-1213*a^3/7920 + 3*a^2/40 + a)^2 + (96791/1568160 : ℝ) * (1) * (a^3 - 63558*a^2/96791)^2 + (8729/9582309 : ℝ) * (1) * (a^2)^2 := by
    try simp only [helim0, helim1]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h₁ : a^2 + b = 4) (h₂ : b^2 + c = 8), 2 * a * b + b * c + c * a ≥ -32) := @solution
#print axioms solution

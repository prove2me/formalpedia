-- Prove2me | solution 1 for WorkbookSource.base_31532
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:10:42.206989+00:00
-- url     : https://prove2.me/submissions/6ed0a26c-9ce1-46c6-86b9-187d928879a1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a + b + c = -6) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0  := by
  have helim0 : c = (-a - b - 6) := by
    have hh := h
    linarith only [hh]
  have hsum : 0 ≤ (48 : ℝ) * (1) * (-a^2/36 - 7*a*b/36 - b^2/36 + 1)^2 + (116/3 : ℝ) * (1) * (-5*a^2/58 + 5*a*b/58 - 20*a/29 + 9*b^2/58 + b)^2 + (588/29 : ℝ) * (1) * (23*a^2/126 + 5*a*b/18 + a + 5*b^2/126)^2 := by positivity
  have hid : ( a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ) - ( 0  ) = (48 : ℝ) * (1) * (-a^2/36 - 7*a*b/36 - b^2/36 + 1)^2 + (116/3 : ℝ) * (1) * (-5*a^2/58 + 5*a*b/58 - 20*a/29 + 9*b^2/58 + b)^2 + (588/29 : ℝ) * (1) * (23*a^2/126 + 5*a*b/18 + a + 5*b^2/126)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a + b + c = -6), a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 12 * a * b * c + 48 ≥ 0) := @solution
#print axioms solution

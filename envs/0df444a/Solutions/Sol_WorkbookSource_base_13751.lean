-- Prove2me | solution 1 for WorkbookSource.base_13751
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:48:00.364097+00:00
-- url     : https://prove2.me/submissions/96a60e06-1cc5-455b-9174-5722825fa307

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 1) :(16 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 8 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ≥ 0  := by
  have helim : d = (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (82 : ℝ) * (-18*a^2/41 - 36*a*b/41 - 36*a*c/41 + 81*a/82 - 18*b^2/41 - 36*b*c/41 + 81*b/82 - 16*c^2/41 + c - 1/2)^2 + (800/41 : ℝ) * (a^2/10 + a*b/5 + a*c/5 - 9*a/40 + b^2/10 + b*c/5 - 9*b/40 + c^2)^2 + (16 : ℝ) * (b^2 + b/4 - 1/8)^2 + (16 : ℝ) * (a^2 + a/4 - 1/8)^2 := by positivity
  have hid : ((16 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 8 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ) - ( 0  ) = (82 : ℝ) * (-18*a^2/41 - 36*a*b/41 - 36*a*c/41 + 81*a/82 - 18*b^2/41 - 36*b*c/41 + 81*b/82 - 16*c^2/41 + c - 1/2)^2 + (800/41 : ℝ) * (a^2/10 + a*b/5 + a*c/5 - 9*a/40 + b^2/10 + b*c/5 - 9*b/40 + c^2)^2 + (16 : ℝ) * (b^2 + b/4 - 1/8)^2 + (16 : ℝ) * (a^2 + a/4 - 1/8)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (habc : a + b + c + d = 1), (16 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) + 8 * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3) - 3 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ≥ 0) := @solution
#print axioms solution

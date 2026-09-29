-- Prove2me | solution 1 for WorkbookSource.base_33911
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:37:20.654647+00:00
-- url     : https://prove2.me/submissions/630bda6c-48ff-4be9-aff9-a15bb0ea16cb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 + 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1) ≥ 4  := by
  have helim : d = (-a - b - c + 4) := by linarith only [habc]
  have hslack : 0 ≤ (-a - b - c + 4) := by linarith only [helim, hd]
  have hsum : 0 ≤ (2 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/2 - b/2 + 1)^2 + (2 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/2 - c/2 + 1)^2 + (2 : ℝ) * ((b) * (c)) * (-b/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (-a - b - c + 4)) * (-b/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (c)) * (-a/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (b)) * (-a/2 - b/2 + 1)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + d^2 + 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1) ) - ( 4  ) = (2 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/2 - b/2 + 1)^2 + (2 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/2 - c/2 + 1)^2 + (2 : ℝ) * ((b) * (c)) * (-b/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (-a - b - c + 4)) * (-b/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (c)) * (-a/2 - c/2 + 1)^2 + (2 : ℝ) * ((a) * (b)) * (-a/2 - b/2 + 1)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (habc : a + b + c + d = 4), a^2 + b^2 + c^2 + d^2 + 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1) ≥ 4) := @solution
#print axioms solution

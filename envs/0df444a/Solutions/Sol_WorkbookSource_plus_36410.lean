-- Prove2me | solution 1 for WorkbookSource.plus_36410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:38:02.451394+00:00
-- url     : https://prove2.me/submissions/ed3dfbde-bd8b-4a88-90f6-64a72dcf4e23

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a^2 + b^2 + c^2 + d^2 - 4 ≥ 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1)   := by
  have helim : d = (-a - b - c + 4) := by linarith only [hab]
  have hslack : 0 ≤ (-a - b - c + 4) := by linarith only [helim, hd]
  have hsum : 0 ≤ (24 : ℝ) * (1) * (a^2/12 + a*b/4 + a*c/4 - 2*a/3 + b^2/12 + b*c/4 - 2*b/3 + c^2/12 - 2*c/3 + 1)^2 + (4/3 : ℝ) * (1) * (a^2/4 - a/2 + b^2/4 - b/2 - c^2/2 + c)^2 + (1 : ℝ) * (1) * (a^2/2 - a - b^2/2 + b)^2 + (2 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/8 : ℝ) * ((c) * (-a - b - c + 4)) * (-a + b)^2 + (2 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/8 : ℝ) * ((b) * (-a - b - c + 4)) * (-a + c)^2 + (2 : ℝ) * ((b) * (c)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/8 : ℝ) * ((b) * (c)) * (-b + c)^2 + (2 : ℝ) * ((a) * (-a - b - c + 4)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/8 : ℝ) * ((a) * (-a - b - c + 4)) * (-b + c)^2 + (2 : ℝ) * ((a) * (c)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/8 : ℝ) * ((a) * (c)) * (-a + c)^2 + (2 : ℝ) * ((a) * (b)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/8 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + d^2 - 4 ) - ( 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1)   ) = (24 : ℝ) * (1) * (a^2/12 + a*b/4 + a*c/4 - 2*a/3 + b^2/12 + b*c/4 - 2*b/3 + c^2/12 - 2*c/3 + 1)^2 + (4/3 : ℝ) * (1) * (a^2/4 - a/2 + b^2/4 - b/2 - c^2/2 + c)^2 + (1 : ℝ) * (1) * (a^2/2 - a - b^2/2 + b)^2 + (2 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/8 : ℝ) * ((c) * (-a - b - c + 4)) * (-a + b)^2 + (2 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/8 : ℝ) * ((b) * (-a - b - c + 4)) * (-a + c)^2 + (2 : ℝ) * ((b) * (c)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/8 : ℝ) * ((b) * (c)) * (-b + c)^2 + (2 : ℝ) * ((a) * (-a - b - c + 4)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/8 : ℝ) * ((a) * (-a - b - c + 4)) * (-b + c)^2 + (2 : ℝ) * ((a) * (c)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/8 : ℝ) * ((a) * (c)) * (-a + c)^2 + (2 : ℝ) * ((a) * (b)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/8 : ℝ) * ((a) * (b)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4), a^2 + b^2 + c^2 + d^2 - 4 ≥ 4 * (a - 1) * (b - 1) * (c - 1) * (d - 1)) := @solution
#print axioms solution

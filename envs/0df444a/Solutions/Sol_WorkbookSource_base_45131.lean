-- Prove2me | solution 1 for WorkbookSource.base_45131
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:28:06.248853+00:00
-- url     : https://prove2.me/submissions/6a72f130-cf06-4d46-a705-1cc32138df04

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : √(10 + √24 + √40 + √60) = √2 + √3 + √5  := by
  have h24 : √(24:ℝ) = 2*√2*√3 := by
    rw [show (24:ℝ) = 4*(2*3) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
    norm_num
    ring
  have h40 : √(40:ℝ) = 2*√2*√5 := by
    rw [show (40:ℝ) = 4*(2*5) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
    norm_num
    ring
  have h60 : √(60:ℝ) = 2*√3*√5 := by
    rw [show (60:ℝ) = 4*(3*5) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
    norm_num
    ring
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [h24,h40,h60]
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  nlinarith
example : (√(10 + √24 + √40 + √60) = √2 + √3 + √5) := @solution
#print axioms solution

-- Prove2me | solution 1 for WorkbookSource.base_6974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:28:05.468017+00:00
-- url     : https://prove2.me/submissions/ed1d6888-5fe2-4ff3-b845-50acaf2dd043

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution : √(3 + √5) + √(3 - √5) = √10  := by
  have s5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have p5 := Real.sqrt_nonneg (5:ℝ)
  have hminus : (0:ℝ) ≤ 3-√5 := by nlinarith
  have ha := Real.sq_sqrt (show (0:ℝ) ≤ 3+√5 by positivity)
  have hb := Real.sq_sqrt hminus
  have hpa := Real.sqrt_nonneg (3+√5)
  have hpb := Real.sqrt_nonneg (3-√5)
  have hp : (√(3+√5)*√(3-√5))^2 = 4 := by rw [mul_pow, ha, hb]; nlinarith
  have hn : 0 ≤ √(3+√5)*√(3-√5) := by positivity
  have he : √(3+√5)*√(3-√5) = 2 := by nlinarith
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)
  have hpt := Real.sqrt_nonneg (10:ℝ)
  nlinarith
example : (√(3 + √5) + √(3 - √5) = √10) := @solution
#print axioms solution

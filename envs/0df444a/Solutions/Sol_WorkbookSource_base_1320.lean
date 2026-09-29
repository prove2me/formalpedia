-- Prove2me | solution 1 for WorkbookSource.base_1320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:39:07.788463+00:00
-- url     : https://prove2.me/submissions/6613ddc1-8fbe-480a-9afa-8d25ae20d821

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (hab2 : a + b + 2 > 0) (hab3 : a ^ 2 + b ^ 2 = 4) : a * b / (a + b + 2) ≤ Real.sqrt 2 - 1  := by
  apply (div_le_iff₀ hab2).mpr
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hs : a+b ≤ 2*√2 := by nlinarith [sq_nonneg (a-b)]
  have hn : 0 ≤ 2*√2-(a+b) := by linarith
  nlinarith [mul_nonneg (le_of_lt hab2) hn]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b > 0) (hab2 : a + b + 2 > 0) (hab3 : a ^ 2 + b ^ 2 = 4), a * b / (a + b + 2) ≤ Real.sqrt 2 - 1) := @solution
#print axioms solution

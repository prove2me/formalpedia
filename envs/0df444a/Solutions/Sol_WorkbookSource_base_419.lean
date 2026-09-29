-- Prove2me | solution 1 for WorkbookSource.base_419
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:36:20.439864+00:00
-- url     : https://prove2.me/submissions/19e16151-9557-4b59-8fef-c3257daa30bc

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a ≥ 1 / 4) (hb : b ≥ 1 / 4) (hc : c ≥ 1 / 4) (hab : a + b + c = 1) : √(4 * a + 1) + √(4 * b + 1) + √(4 * c + 1) ≤ 5  := by
  have a0 : 0 ≤ 4*a+1 := by linarith
  have b0 : 0 ≤ 4*b+1 := by linarith
  have c0 : 0 ≤ 4*c+1 := by linarith
  have asq := Real.sq_sqrt a0
  have bsq := Real.sq_sqrt b0
  have csq := Real.sq_sqrt c0
  have ap := Real.sqrt_nonneg (4*a+1)
  have bp := Real.sqrt_nonneg (4*b+1)
  have cp := Real.sqrt_nonneg (4*c+1)
  have hs : (√(4*a+1)+√(4*b+1)+√(4*c+1))^2 ≤ 21 := by
    nlinarith only [asq,bsq,csq,hab,sq_nonneg (√(4*a+1)-√(4*b+1)),sq_nonneg (√(4*b+1)-√(4*c+1)),sq_nonneg (√(4*c+1)-√(4*a+1))]
  nlinarith only [hs]

example : (∀ (a b c : ℝ) (ha : a ≥ 1 / 4) (hb : b ≥ 1 / 4) (hc : c ≥ 1 / 4) (hab : a + b + c = 1), √(4 * a + 1) + √(4 * b + 1) + √(4 * c + 1) ≤ 5) := @solution
#print axioms solution

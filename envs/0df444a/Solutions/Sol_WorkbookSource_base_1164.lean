-- Prove2me | solution 1 for WorkbookSource.base_1164
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:39:06.894479+00:00
-- url     : https://prove2.me/submissions/c78c0405-9939-451d-b59c-7803d168a6e9

import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b : ℝ): (a ≠ 5 ∧ b ≠ 5) → √(2 * (a / (5 - a) + b / (5 - b))) = √((2 * (5 * (a + b) - 2 * a * b)) / (25 - 5 * (a + b) + a * b))  := by
  rintro ⟨ha,hb⟩
  congr 1
  have ha' : 5-a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hb' : 5-b ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
  have hd : 25-5*(a+b)+a*b = (5-a)*(5-b) := by ring
  rw [hd]
  field_simp
  <;> ring
example : (∀ (a b : ℝ), (a ≠ 5 ∧ b ≠ 5) → √(2 * (a / (5 - a) + b / (5 - b))) = √((2 * (5 * (a + b) - 2 * a * b)) / (25 - 5 * (a + b) + a * b))) := @solution
#print axioms solution

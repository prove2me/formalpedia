-- Prove2me | solution 1 for OddPerfectNumber.Kernel.euler_square_not_one_mod_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T07:53:03.10469+00:00
-- url     : https://prove2.me/submissions/2984991a-5e0e-460d-a902-4e3fb15d30c1

import Mathlib

theorem solution (p u : Nat) (h : p + 1 = 6 * u ^ 2) :
    p % 5 != 1 := by
  apply bne_iff_ne.mpr
  intro hp5
  have hmod := congrArg (fun n : Nat => n % 5) h
  have hu0 : 0 ≤ u % 5 := Nat.zero_le _
  have hu5 : u % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hx : u % 5 using hu0, hu5 <;>
    norm_num [hx, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hp5] at hmod

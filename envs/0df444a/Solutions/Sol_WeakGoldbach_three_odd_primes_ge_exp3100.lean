-- Prove2me | solution 1 for WeakGoldbach.three_odd_primes_ge_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:57:06.881326+00:00
-- url     : https://prove2.me/submissions/40ec0bfe-31f3-4bc0-8cd8-cf070c9f03cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd
import Mathlib

theorem solution (n : Nat)
    (hn : Real.exp 3100 ≤ (n : Real)) (hodd : Odd n) :
    ∃ p q r : Nat,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  have h3101 : (3101 : Real) ≤ Real.exp 3100 := by
    convert Real.add_one_le_exp (3100 : Real) using 1 <;> norm_num
  have h5real : (5 : Real) < Real.exp 3100 :=
    lt_of_lt_of_le (by norm_num) h3101
  have h5 : 5 < n := by
    exact_mod_cast (lt_of_lt_of_le h5real hn)
  exact WeakGoldbach.ternary_goldbach_all_odd n h5 hodd

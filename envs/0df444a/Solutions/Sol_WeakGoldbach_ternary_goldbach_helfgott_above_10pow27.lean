-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_helfgott_above_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:25:56.645081+00:00
-- url     : https://prove2.me/submissions/fcceb33a-5da4-4f2f-a7a2-03f2852beab8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100
import Mathlib

theorem solution (n : Nat) (hodd : Odd n)
    (hlo : 10 ^ 27 <= n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
        Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases hhi : (n : Real) < Real.exp 3100
  · exact WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hlo hhi hodd
  · exact WeakGoldbach.three_odd_primes_ge_exp3100 n (le_of_not_gt hhi) hodd

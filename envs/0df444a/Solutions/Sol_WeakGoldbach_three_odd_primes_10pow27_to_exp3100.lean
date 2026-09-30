-- Prove2me | solution 1 for WeakGoldbach.three_odd_primes_10pow27_to_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T12:35:02.487332+00:00
-- url     : https://prove2.me/submissions/40b0ddaa-6ca2-4543-a810-018a574498ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd
import Mathlib

theorem solution (n : Nat)
    (hlo : 10 ^ 27 <= n) (hhi : (n : Real) < Real.exp 3100) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  have h5 : 5 < 10 ^ 27 := by norm_num
  exact WeakGoldbach.ternary_goldbach_all_odd n (lt_of_lt_of_le h5 hlo) hodd

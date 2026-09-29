-- Prove2me | solution 1 for OddPerfectNumber.no_odd_perfect_special_exponent_one
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-10T22:58:36.255585+00:00
-- url     : https://prove2.me/submissions/4f6add8e-642b-4505-ad8c-d7b0370f0903
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_no_odd_perfect_k_one_odd_m
import Theorems.Thm_OddPerfectNumber_no_odd_perfect_k_one_not_odd_m

open OddPerfectNumber

theorem solution (n p m : Nat) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hpm : ¬ p ∣ m) : n ≠ p * m ^ 2 := by
  by_cases hm : Odd m
  -- Children were published with boolean `!=` conclusions; convert.
  · exact bne_iff_ne.mp (no_odd_perfect_k_one_odd_m n p m hn hodd hp hp4 hpm hm)
  · exact bne_iff_ne.mp (no_odd_perfect_k_one_not_odd_m n p m hn hodd hp hp4 hpm hm)

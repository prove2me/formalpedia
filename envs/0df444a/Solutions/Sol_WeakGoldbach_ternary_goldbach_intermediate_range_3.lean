-- Prove2me | solution 3 for WeakGoldbach.ternary_goldbach_intermediate_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:30:41.659966+00:00
-- url     : https://prove2.me/submissions/33bb9483-c9a6-4b65-8cf4-509a0861d2b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100

set_option autoImplicit false

theorem solution (n : ℕ) (hodd : Odd n) (hlo : 10 ^ 27 ≤ n) (hhi : (n : ℝ) < Real.exp 3100) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r :=
  WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hlo hhi hodd

#print axioms solution

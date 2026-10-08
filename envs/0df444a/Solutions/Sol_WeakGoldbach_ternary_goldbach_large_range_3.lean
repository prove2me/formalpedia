-- Prove2me | solution 3 for WeakGoldbach.ternary_goldbach_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:30:41.557909+00:00
-- url     : https://prove2.me/submissions/5652d859-58aa-451b-bae6-830ab3ff309c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

set_option autoImplicit false

theorem solution (n : ℕ) (hodd : Odd n) (hlo : Real.exp 3100 ≤ (n : ℝ)) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r :=
  WeakGoldbach.three_odd_primes_ge_exp3100 n hlo hodd

#print axioms solution

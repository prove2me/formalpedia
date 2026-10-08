-- Prove2me | solution 3 for WeakGoldbach.three_odd_primes_ge_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:17:49.412232+00:00
-- url     : https://prove2.me/submissions/fc1eb60b-5191-430b-940e-acfc8488ddfc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_large_range

set_option autoImplicit false

theorem solution (n : ℕ) (hn : Real.exp 3100 ≤ (n : ℝ)) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r :=
  WeakGoldbach.ternary_goldbach_large_range n hodd hn

#print axioms solution

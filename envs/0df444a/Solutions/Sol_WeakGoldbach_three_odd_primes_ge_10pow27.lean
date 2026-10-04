-- Prove2me | solution 1 for WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:52:34.946373+00:00
-- url     : https://prove2.me/submissions/752e3a7e-96b8-4407-aeec-2f46775ea058
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

theorem solution (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases h : (n : ℝ) < Real.exp 3100
  · exact WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hn h hodd
  · exact WeakGoldbach.three_odd_primes_ge_exp3100 n (not_lt.mp h) hodd

-- Prove2me | solution 2 for WeakGoldbach.three_odd_primes_ge_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T11:01:53.63039+00:00
-- url     : https://prove2.me/submissions/40b9b70e-eff3-49b8-a802-d17ec0df7319
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

namespace WeakGoldbach

theorem _root_.solution (n : ℕ) (hn : 10 ^ 27 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases h : (n : ℝ) < Real.exp 3100
  · exact WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hn h hodd
  · exact WeakGoldbach.three_odd_primes_ge_exp3100 n (not_lt.1 h) hodd

end WeakGoldbach

#print axioms solution

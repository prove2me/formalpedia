-- Prove2me | solution 3 for WeakGoldbach.ternary_goldbach_all_odd_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:20:55.054275+00:00
-- url     : https://prove2.me/submissions/acf2e6c1-46be-4d0f-a0a6-7a543c03590c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

set_option autoImplicit false

/-- Same Helfgott–Platt / analytic split as `ternary_goldbach_all_odd_ge_9` under the graph name `ternary_goldbach_all_odd_9`. -/
theorem solution (n : ℕ) (hlo : 9 ≤ n) (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases h : n ≤ 8875694145621773516800000000000
  · exact WeakGoldbach.verified_three_odd_primes_to_8875e30 n hlo h hodd
  · have h27 : 10 ^ 27 ≤ n := by
      have hmax : 10 ^ 27 ≤ 8875694145621773516800000000000 := by norm_num
      exact hmax.trans (Nat.lt_of_not_ge h).le
    exact WeakGoldbach.three_odd_primes_ge_10pow27 n h27 hodd

#print axioms solution

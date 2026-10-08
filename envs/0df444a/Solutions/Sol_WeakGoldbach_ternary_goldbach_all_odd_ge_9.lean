-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_all_odd_ge_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:04:31.085992+00:00
-- url     : https://prove2.me/submissions/cb56faf6-5032-4f1c-9e3b-aa109682172b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

set_option autoImplicit false

/-- Split at Helfgott–Platt's verified ceiling: finite check below
`8875694145621773516800000000000`, analytic ternary Goldbach (Helfgott 2013) above. -/
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

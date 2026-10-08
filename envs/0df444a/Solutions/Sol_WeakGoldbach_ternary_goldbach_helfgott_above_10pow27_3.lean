-- Prove2me | solution 3 for WeakGoldbach.ternary_goldbach_helfgott_above_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:57:57.547951+00:00
-- url     : https://prove2.me/submissions/2a048549-cc4f-4741-9e61-02dd1a631013
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_three_odd_primes_10pow27_to_exp3100
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_exp3100

set_option autoImplicit false

/-- Helfgott's range split at `exp 3100`: intermediate analytic part vs. the asymptotic tail. -/
theorem solution (n : ℕ) (hodd : Odd n) (hlo : 10 ^ 27 ≤ n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  by_cases h : (n : ℝ) < Real.exp 3100
  · exact WeakGoldbach.three_odd_primes_10pow27_to_exp3100 n hlo h hodd
  · have hge : Real.exp 3100 ≤ (n : ℝ) := not_lt.mp h
    exact WeakGoldbach.three_odd_primes_ge_exp3100 n hge hodd

#print axioms solution

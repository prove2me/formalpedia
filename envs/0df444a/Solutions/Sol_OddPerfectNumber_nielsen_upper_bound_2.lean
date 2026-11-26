-- Prove2me | solution 2 for OddPerfectNumber.nielsen_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @curiyu
-- created : 2026-09-08T04:01:13.959969+00:00
-- url     : https://prove2.me/submissions/812cfccb-ca96-41ef-b921-0abc78783297

import Theorems.Thm_OddPerfectNumber_nielsen_theorem1
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc

theorem solution (n : ℕ) (hn : Nat.Perfect n) (hodd : Odd n) :
    n < 2 ^ (4 ^ n.primeFactors.card) := by
  have hpos : 0 < n := hn.2
  have hsig : ArithmeticFunction.sigma 1 n = 2 * n := by
    rw [ArithmeticFunction.sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hn
  have h := OddPerfectNumber.nielsen_theorem1 n 2 1 (by norm_num) (by norm_num) hodd (by simp [hsig])
  simpa using h

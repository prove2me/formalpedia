-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T22:57:18.565652+00:00
-- url     : https://prove2.me/submissions/db0c7f32-6664-4bc2-a4ae-429646e942c5

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp3_two_role
import Theorems.Thm_OddPerfectNumber_k_one_half_successor_support

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2) :
    False := by
  have hp13 := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp3_two_role
    p m d q4 hp hm hpm hprod hsig hsupport hq4prime hq4gt h3mem h3exp
  have hprod13 : m ^ 2 = ((13 + 1) / 2) * d := by
    simpa [hp13] using hprod
  have h7m : 7 ∣ m := by
    apply OddPerfectNumber.k_one_half_successor_support 13 m d 7
      (by norm_num) hprod13
    norm_num
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨u, hu⟩
    omega
  have h7mem : 7 ∈ m.primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_seven, h7m, hm0⟩
  rcases hsupport 7 h7mem with h3 | h5 | h19 | hq
  · norm_num at h3
  · norm_num at h5
  · norm_num at h19
  · omega

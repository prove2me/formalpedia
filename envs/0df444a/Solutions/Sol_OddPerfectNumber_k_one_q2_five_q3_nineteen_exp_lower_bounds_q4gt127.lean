-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_lower_bounds_q4gt127
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T06:42:24.841492+00:00
-- url     : https://prove2.me/submissions/9a3667dd-45b5-4faf-927f-4c103853c718

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 127 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5pos : 0 < (m ^ 2).factorization 5)
    (h5even : Even ((m ^ 2).factorization 5))
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19pos : 0 < (m ^ 2).factorization 19)
    (h19even : Even ((m ^ 2).factorization 19)) :
    6 ≤ (m ^ 2).factorization 5 ∧ 4 ≤ (m ^ 2).factorization 19 := by
  have h5floor := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp5_ge_six_q4gt71
    p m d q4 hp hp4 hm hpm hprod hsig hsupport hq4prime (by omega)
    h5mem h5even h5pos
  have h19floor := OddPerfectNumber.k_one_q2_five_q3_nineteen_exp19_ge_four_q4ne127_v3
    p m d q4 hp hm hpm hprod hsig hsupport hq4prime (by omega)
    h19mem h19pos h19even (by omega)
  exact ⟨h5floor, h19floor⟩

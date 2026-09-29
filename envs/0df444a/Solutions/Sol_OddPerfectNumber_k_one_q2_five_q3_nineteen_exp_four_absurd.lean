-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_exp_four_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:26:17.729745+00:00
-- url     : https://prove2.me/submissions/4a00d05a-0289-4062-9082-a07f02f38b7e

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_one_five_one_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 19 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 151 < q4)
    (h19mem : 19 ∈ (m ^ 2).primeFactors)
    (h19exp : (m ^ 2).factorization 19 = 4) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 19 hn0 h19mem
  rw [h19exp] at hlocal
  have hlocal4 : (∑ i ∈ Finset.range (4 + 1), 19 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h151local : 151 ∣ ∑ i ∈ Finset.range (4 + 1), 19 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h151global : 151 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h151local hlocal4
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  exact OddPerfectNumber.four_support_external_one_five_one_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt h151global

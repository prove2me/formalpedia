-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_two_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:02:50.937224+00:00
-- url     : https://prove2.me/submissions/1df2cc22-94b8-4f4c-87ce-909188542296

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_thirty_one_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 31 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 2) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 5 hn0 h5mem
  have hlocal2 : (∑ i ∈ Finset.range (2 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := by
    rw [h5exp] at hlocal
    exact hlocal
  have h31local : 31 ∣ ∑ i ∈ Finset.range (2 + 1), 5 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h31global : 31 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h31local hlocal2
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  exact OddPerfectNumber.four_support_external_thirty_one_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt h31global

-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp_four_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T18:59:47.38413+00:00
-- url     : https://prove2.me/submissions/399a4ae6-fbde-40b0-96a6-65bee0acef83

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_five_exp_four_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (h5mem : 5 ∈ (m ^ 2).primeFactors)
    (h5exp : (m ^ 2).factorization 5 = 4) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 5 hn0 h5mem
  rw [h5exp] at hlocal
  have hlocal4 : (∑ i ∈ Finset.range (4 + 1), 5 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  exact OddPerfectNumber.four_support_five_exp_four_absurd
    p m d q4 hp hp4 hm0 hsig hddvd hsupport hq4prime hq4gt hlocal4

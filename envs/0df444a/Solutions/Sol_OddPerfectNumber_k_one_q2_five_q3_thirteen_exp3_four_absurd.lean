-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_four_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-13T19:35:26.49731+00:00
-- url     : https://prove2.me/submissions/182b418e-c62c-4af4-b82b-4fa8ab1f2a58

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_external_eleven_absurd

theorem solution (p m d q4 : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 13 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 4) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨k, hk⟩
    omega
  have hn0 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 3 hn0 h3mem
  rw [h3exp] at hlocal
  have hlocal4 : (∑ i ∈ Finset.range (4 + 1), 3 ^ i) ∣
      ∑ x ∈ (m ^ 2).divisors, x := hlocal
  have h11local : 11 ∣ ∑ i ∈ Finset.range (4 + 1), 3 ^ i := by
    norm_num [Finset.sum_range_succ]
  have h11global : 11 ∣ ∑ x ∈ (m ^ 2).divisors, x :=
    dvd_trans h11local hlocal4
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  exact OddPerfectNumber.four_support_external_eleven_absurd
    p m d q4 hp hp4 (by exact hm0) hsig hddvd hsupport hq4prime hq4gt h11global

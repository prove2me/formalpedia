-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_half_exp23_ge2_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T15:38:52.813214+00:00
-- url     : https://prove2.me/submissions/afab6290-e066-4e2b-8e0a-ae01d6f01384

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted

-- EXPONENT CONVENTION: c is the HALF exponent of 23; the full exponent is 2*c.
theorem solution (p m d q4 c : Nat)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hq4gt : 23 < q4)
    (h23mem : 23 ∈ (m ^ 2).primeFactors)
    (h23exp : (m ^ 2).factorization 23 = 2*c)
    (hc : 0 < c) : 2 ≤ c := by
  by_contra hsmall
  have hc1 : c = 1 := by omega
  have hm0 : m ≠ 0 := by rcases hm with ⟨u, hu⟩; omega
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 23 (pow_ne_zero 2 hm0) h23mem
  have hexp : (m ^ 2).factorization 23 = 2 := by simpa [hc1] using h23exp
  rw [hexp] at hlocal
  have h7local : 7 ∣ ∑ i ∈ Finset.range (2 + 1), 23 ^ i := by
    norm_num [Finset.sum_range_succ]
  have hddvd : d ∣ m ^ 2 := by
    refine ⟨(p + 1) / 2, ?_⟩
    simpa [Nat.mul_comm] using hprod
  have hcases := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 23 q4 7 hp Nat.prime_seven hm0 hsig hddvd
      (h7local.trans hlocal) hsupport
  rcases hcases with hEuler | h3 | h5 | h23 | hq
  · have hp7 : p = 7 := hEuler.symm
    norm_num [hp7] at hp4
  · norm_num at h3
  · norm_num at h5
  · norm_num at h23
  · omega

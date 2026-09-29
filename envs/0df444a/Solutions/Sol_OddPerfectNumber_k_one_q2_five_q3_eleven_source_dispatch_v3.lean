-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_source_dispatch_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:58:47.837979+00:00
-- url     : https://prove2.me/submissions/ec4203f8-5d6c-439d-a543-7c0c51ab755a

import Mathlib
import Theorems.Thm_OddPerfectNumber_local_sigma_factor_dvd_global
import Theorems.Thm_OddPerfectNumber_four_support_sigma_prime_restricted
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_eleven_q4_13_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_half_successor_support

theorem solution
    (m b c e p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hupper : sigma ≤ 2 * m ^ 2)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm : Odd m) (hpm : ¬ p ∣ m)
    (hprod : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 11 ∨ x = q4)
    (hq4prime : q4.Prime) (hq4gt : 11 < q4)
    (h3mem : 3 ∈ (m ^ 2).primeFactors)
    (h3exp : (m ^ 2).factorization 3 = 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  have hm0 : m ≠ 0 := by
    rcases hm with ⟨u, hu⟩
    omega
  have hm2ne : m ^ 2 ≠ 0 := pow_ne_zero 2 hm0
  have hlocal := OddPerfectNumber.local_sigma_factor_dvd_global
    (m ^ 2) 3 hm2ne h3mem
  have h13local : 13 ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i := by
    rw [h3exp]
    norm_num
  have hlocal_sigma :
      (∑ i ∈ Finset.range ((m ^ 2).factorization 3 + 1), 3 ^ i) ∣ sigma := by
    simpa [← hglobal] using hlocal
  have h13sigma : 13 ∣ sigma := dvd_trans h13local hlocal_sigma
  have h13global : 13 ∣ ∑ x ∈ (m ^ 2).divisors, x := by
    simpa [← hglobal] using h13sigma
  have hddvd : d ∣ m ^ 2 := by
    rw [hprod]
    exact dvd_mul_left d ((p + 1) / 2)
  have hsrc := OddPerfectNumber.four_support_sigma_prime_restricted
    p m d 3 5 11 q4 13 hp (by norm_num) hm0 hsig hddvd h13global hsupport
  rcases hsrc with hp13 | h3 | h5 | h11 | hq
  · have hprod13 : m ^ 2 = ((13 + 1) / 2) * d := by
      simpa [hp13] using hprod
    have h7m : 7 ∣ m :=
      OddPerfectNumber.k_one_half_successor_support 13 m d 7
        (by norm_num) hprod13 (by norm_num)
    have h7mem : 7 ∈ m.primeFactors := by
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_seven, h7m, hm0⟩
    rcases hsupport 7 h7mem with h3' | h5' | h11' | hq'
    · norm_num at h3'
    · norm_num at h5'
    · norm_num at h11'
    · omega
  · norm_num at h3
  · norm_num at h5
  · norm_num at h11
  · have hqeq : q4 = 13 := by omega
    subst q4
    apply OddPerfectNumber.k_one_q2_five_q3_eleven_q4_13_absurd_v2 m b c e sigma
      (by simpa [mul_assoc] using hfac)
      (by simpa [mul_assoc] using hsigma)
      hupper hb hc he

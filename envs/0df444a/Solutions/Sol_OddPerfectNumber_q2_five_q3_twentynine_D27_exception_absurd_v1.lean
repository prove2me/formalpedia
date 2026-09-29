-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_exception_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:54:45.875673+00:00
-- url     : https://prove2.me/submissions/fea15d95-2001-47a0-86d0-5be2c99aa81a

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_exception_external_source_v1
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_D27_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D27_external_source_absurd

theorem solution (m d sigma D p q4 a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hD : D = 27)
    (hp_eq : p = 2 * D - 1)
    (hq4cases : q4 = 47 ∨ q4 = 89)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2) (hm0 : m ≠ 0)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4) : False := by
  have hp53 : p = 53 := by omega
  have hlocal := OddPerfectNumber.q2_five_q3_twentynine_D27_exception_external_source_v1
    e q4
    (OddPerfectNumber.q2_five_q3_twentynine_D27_source_bridge_v1
      D p sigma m a b c e q4 hrel hD hp_eq hsigma)
    hq4cases
  have hsig53 : (∑ x ∈ (m ^ 2).divisors, x) = 53 * d := by
    simpa [hp53] using hsig
  rcases hlocal with ⟨hq4, hdiv⟩ | ⟨hq4, hdiv⟩
  · apply OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_external_source_absurd
      m d sigma q4 hsig53 hddvd hm0 hsupport
    left
    refine ⟨hq4, ?_⟩
    rw [← hglobal, hsigma]
    exact dvd_mul_of_dvd_right hdiv _
  · apply OddPerfectNumber.k_one_q2_five_q3_twentynine_D27_external_source_absurd
      m d sigma q4 hsig53 hddvd hm0 hsupport
    right
    refine ⟨hq4, ?_⟩
    rw [← hglobal, hsigma]
    exact dvd_mul_of_dvd_right hdiv _

-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T06:17:50.634179+00:00
-- url     : https://prove2.me/submissions/48da3398-5f4a-4a85-9876-7116c28f211f

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_case
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_53_no_five_source

theorem solution
    (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 111 ≤ D) (hDhigh : D ≤ 685)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 47 < q4) (hq4le : q4 ≤ 61)
    (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (hb : 1 ≤ b) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have hcase := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_case
    m a b c e D p q4 sigma d hfac hsigma hrel hDlow hDhigh hp hp4 hp_eq
    hq4prime hq4gt hq4le hq4dvd hDsupport hb hm0 hsig hddvd hsupport hglobal
  rcases hcase with ⟨hq4eq, hDeq, hpeq⟩
  subst q4
  subst D
  subst p
  have h5pow : 5 ∣ 5 ^ (2*b) := dvd_pow_self 5 (by omega)
  have h5m : 5 ∣ m ^ 2 := by
    rw [hfac]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (dvd_mul_of_dvd_right
        (dvd_mul_of_dvd_right
          (dvd_mul_of_dvd_right h5pow (3 ^ (2*a)))
          (23 ^ (2*c)))
        (53 ^ (2*e)))
  have h5sig : 5 ∣ sigma := by
    have h5rhs : 5 ∣ 953 * m ^ 2 := dvd_mul_of_dvd_right h5m 953
    have h5lhs : 5 ∣ 477 * sigma := by
      rw [hrel]
      exact h5rhs
    rcases ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).mp h5lhs) with hD5 | hsigma5
    · norm_num at hD5
    · exact hsigma5
  exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_53_no_five_source
    sigma a b c e hsigma h5sig

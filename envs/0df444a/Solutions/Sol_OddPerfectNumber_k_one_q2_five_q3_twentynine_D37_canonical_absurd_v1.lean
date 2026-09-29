-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_canonical_absurd_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T12:03:53.594145+00:00
-- url     : https://prove2.me/submissions/761251aa-8ca4-4ac2-87e1-e621e9e7c788

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_D37_absurd_v2

theorem solution (m d D p q4 sigma a b c e : Nat)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 * a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2 * b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2 * c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2 * e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hD : D = 37)
    (hp_eq : p = 2 * D - 1)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 29 ∨ x = q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (hq4prime : q4.Prime)
    (haEven : Even a) (hbEven : Even b) (hcEven : Even c) (heEven : Even e) :
    False := by
  have hq4eq : q4 = 37 := by
    rcases hDsupport 37 (by norm_num) (by simpa [hD]) with h | h | h | h
    · norm_num at h
    · norm_num at h
    · norm_num at h
    · exact h.symm
  exact OddPerfectNumber.k_one_q2_five_q3_twentynine_D37_absurd_v2
    m d D p q4 sigma a b c e hsigma hrel hD hp_eq hp hp4 hm0 hsig hglobal
    hddvd hsupport hq4prime hq4eq haEven hbEven hcEven heEven

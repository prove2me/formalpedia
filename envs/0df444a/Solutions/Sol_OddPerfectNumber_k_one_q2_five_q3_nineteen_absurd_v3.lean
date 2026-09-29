-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T05:04:50.882452+00:00
-- url     : https://prove2.me/submissions/97d1e06d-b4a0-44a6-92f6-0c44a5d1b8ec

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_absurd_v1

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcase :
      ((D < 225 ∧ Odd D ∧ p.Prime ∧ p = 2 * D - 1 ∧ q4.Prime ∧
        19 < q4 ∧ D < q4 ∧
        (∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) ∧
        4 ≤ a ∧ 3 ≤ b ∧ 2 ≤ c ∧ 1 ≤ e ∧
        ((D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
         (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨
         (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148))) ∨
      (D = 855 ∧ p = 2 * D - 1 ∧ q4 = 101 ∧ 1 ≤ e))) :
    False := by
  rcases hcase with hs | hl
  · rcases hs with ⟨hDlt, hDodd, hp, hp_eq, hq4prime, hq4gt, hDq,
        hDsupport, ha, hb, hc, he, hDq4range⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
      m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq
      hq4prime hq4gt hDq hDsupport ha hb hc he hDq4range
  · rcases hl with ⟨hD, hp_eq, hq4, he⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel hp_eq hD hq4 he

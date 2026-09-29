-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T04:41:41.439034+00:00
-- url     : https://prove2.me/submissions/1c612fb7-181f-4071-8059-ef9921aabca3

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_support_cut_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_q4_61_source_bridge_v1

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
    (hb : 1 ≤ b)
    (hm0 : m ≠ 0)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) :
    False := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_support_cut_v2
    D p q4 hDlow hDhigh hp hp4 hp_eq hq4prime hq4gt hq4le hq4dvd hDsupport
  rcases hcases with h1 | hrest
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
      m a b c e D p q4 sigma hfac hsigma hrel hb (Or.inl h1)
  · rcases hrest with h2 | hrest
    · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
        m a b c e D p q4 sigma hfac hsigma hrel hb (Or.inr (Or.inl h2))
    · rcases hrest with h3 | hrest
      · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
          m a b c e D p q4 sigma hfac hsigma hrel hb
            (Or.inr (Or.inr (Or.inl h3)))
      · rcases hrest with h4 | h5
        · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_source_bridge_v1
            m a b c e D p q4 sigma hfac hsigma hrel hb
              (Or.inr (Or.inr (Or.inr h4)))
        · rcases h5 with ⟨hD5, hp5, hq5⟩
          subst D
          subst p
          subst q4
          exact OddPerfectNumber.k_one_q2_five_q3_twentythree_q4_61_source_bridge_v1
            m a b c  e 549 1097 61 sigma d hfac hsigma hrel hp hp4 hm0 hsig hddvd
            hsupport hq4prime hb hglobal rfl rfl rfl

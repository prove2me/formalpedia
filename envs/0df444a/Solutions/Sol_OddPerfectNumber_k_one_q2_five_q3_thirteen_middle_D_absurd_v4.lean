-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_absurd_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T02:28:08.703173+00:00
-- url     : https://prove2.me/submissions/6d7f7212-7fcd-4529-9bbd-b0e94a635b1b

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_candidates
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_residual_absurd_v3

-- EXPONENT CONVENTION: a,b,c,e are HALF exponents; full exponents are twice these.
-- Canonical middle-range assembly: 13 exact candidates routed to the two
-- half-floor dispatch theorems (nine-case abundance/support cut, four-case residual).
theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 45 ≤ D) (hDhigh : D < 214)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4 : q4.Prime) (hq4gt : 13 < q4) (hq4le : q4 ≤ 89)
    (hq4dvd : q4 ∣ D)
    (hm : Odd m)
    (hsupport : ∀ x ∈ m.primeFactors, x = 3 ∨ x = 5 ∨ x = 13 ∨ x = q4)
    (hDm : D ∣ m ^ 2)
    (ha : 1 ≤ a) (hb : 4 ≤ b) (hc : 1 ≤ c) (he : 1 ≤ e) :
    False := by
  have hcases :=
    OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_candidates
      D p q4 hDlow hDhigh hp hp4 hp_eq hq4 hq4gt hq4le hq4dvd
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm (Or.inl h) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inl h)) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inl h))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hrel hb (Or.inl h)
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inl h)))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hrel hb
      (Or.inr (Or.inl h))
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hrel hb
      (Or.inr (Or.inr (Or.inl h)))
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_residual_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hrel hb
      (Or.inr (Or.inr (Or.inr h)))
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_abundance_cut_v3
      m a b c e D p q4 sigma hfac hsigma hrel hm hsupport hDm
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) ha hb hc he

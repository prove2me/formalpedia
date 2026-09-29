-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T00:58:14.862935+00:00
-- url     : https://prove2.me/submissions/f8fe8dbc-5cac-4531-bc8d-a8f1cd18af8e

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D27_canonical_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D69_abundance_absurd
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D75_absurd_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    False := by
  have hcut := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
    m a b c e D p q4 sigma hfac hsigma hrel hDlt hDodd hp hp_eq hq4prime
    hq4gt hDq hDsupport ha hb hc he
  rcases hcut with h27 | h45 | h69 | h75
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D27_canonical_absurd_v2
      m a b c e D p q4 sigma hfac hsigma hrel h27 hp_eq hq4prime hq4gt
      ha hb hc he
  · have hqwin := OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4
      m a b c e D p q4 sigma hfac hsigma hrel (Or.inl h45) hp_eq hq4prime
      hDq ha hb hc he
    rcases hqwin with hwin | hbad
    · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_abundance_absurd
        m a b c e D p q4 sigma hfac hsigma hrel hwin.1 hp_eq hq4prime
        hwin.2.1 hwin.2.2 ha hb hc he
    · omega
  · have hqwin := OddPerfectNumber.k_one_q2_five_q3_twentythree_D45_D69_q4_ranges_v4
      m a b c e D p q4 sigma hfac hsigma hrel (Or.inr h69) hp_eq hq4prime
      hDq ha hb hc he
    rcases hqwin with hbad | hwin
    · omega
    · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D69_abundance_absurd
        m a b c e D p q4 sigma hfac hsigma hrel hwin.1 hp_eq hq4prime
        hwin.2.1 hwin.2.2 ha hb hc he
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D75_absurd_v1
      m a b c e D p q4 sigma hfac hsigma hrel h75 hp_eq hq4prime hDq

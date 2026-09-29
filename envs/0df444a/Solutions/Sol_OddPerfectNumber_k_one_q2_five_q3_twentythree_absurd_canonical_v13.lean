-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_canonical_v13
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T13:27:35.309874+00:00
-- url     : https://prove2.me/submissions/374d7a88-187b-4274-b2e7-c08bec491a91

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_absurd_canonical_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_gt_47_adapter_v1
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_q4_le_61_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_large_D_D_le_685_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_absurd_v5

-- fresh snapshot after the prior queue transition race
-- changed snapshot after transient import-resolution failure

theorem solution (m a b c e D p q4 sigma d : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDodd : Odd D)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 23 < q4) (hq4dvd : q4 ∣ D)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e)
    (hm0 : m ≠ 0) (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d)
    (hddvd : d ∣ m ^ 2)
    (hsupport : ∀ x ∈ m.primeFactors,
      x = 3 ∨ x = 5 ∨ x = 23 ∨ x = q4)
    (hglobal : sigma = ∑ x ∈ (m ^ 2).divisors, x) : False := by
  by_cases hD : D < 111
  · exact OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_absurd_canonical_v1
      m a b c e D p q4 sigma hfac hsigma hrel hD hDodd hp hp_eq
      hq4prime hq4gt hDsupport ha hb hc he
  · have hDlow : 111 ≤ D := by omega
    have hq4gt47 := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_gt_47_adapter_v1
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt ha hb hc he
    have hq4le := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_q4_le_61_v2
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4gt ha hb hc he
    have hDupper := OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_685_v5
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hDodd hp hp4 hp_eq
      hq4prime hq4gt47 hq4le hq4dvd hDsupport ha hb hc he
    have hq4lelarge : 111 ≤ D → q4 ≤ 61 := by intro; exact hq4le
    have hq4gt47large : 111 ≤ D → 47 < q4 := by intro; exact hq4gt47
    have hq4dvdlarge : 111 ≤ D → q4 ∣ D := by intro; exact hq4dvd
    exact OddPerfectNumber.k_one_q2_five_q3_twentythree_absurd_v5
      m a b c e D p q4 sigma d hfac hsigma hrel hDodd hp hp4 hp_eq
      hq4prime hq4gt hq4lelarge hq4gt47large hq4dvdlarge hDsupport
      ha hb hc he hDupper hm0 hsig hddvd hsupport hglobal

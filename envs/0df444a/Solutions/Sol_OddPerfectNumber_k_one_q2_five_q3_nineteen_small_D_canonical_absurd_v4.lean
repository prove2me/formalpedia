-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_absurd_v4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T03:31:08.274476+00:00
-- url     : https://prove2.me/submissions/08fd1688-ca96-4539-b7ad-78b79159c609

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_survivors
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_q4_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlt : D < 225) (hDodd : Odd D) (hp : p.Prime)
    (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hDq4range :
      (D = 57 ∧ 580 ≤ q4 ∧ q4 ≤ 602) ∨
      (D = 75 ∧ 261 ≤ q4 ∧ q4 ≤ 264) ∨
      (D = 135 ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  have hDs := OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_survivors
    m (2*a) (2*b) (2*c) (2*e) D p q4 sigma hfac hsigma hrel hDlt hDodd hp
    hp_eq hq4prime hq4gt hDq hDsupport (by omega) (by omega) (by omega) (by omega)
  rcases hDs with h57 | h75 | h135
  · have hrange : 580 ≤ q4 ∧ q4 ≤ 602 := by
      rcases hDq4range with hr | hr | hr <;> omega
    have hqcases := OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_q4_cases
      D q4 hq4prime (Or.inl ⟨h57, hrange.1, hrange.2⟩)
    rcases hqcases with ⟨hD587, h587⟩ | ⟨hD593, h593⟩ | ⟨hD599, h599⟩ | ⟨hD601, h601⟩ | ⟨hD75, h75q⟩
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
        m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
        (Or.inl ⟨hD587, h587⟩)
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
        m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
        (Or.inr (Or.inl ⟨hD593, h593⟩))
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
        m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
        (Or.inr (Or.inr (Or.inl ⟨hD599, h599⟩)))
    · exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
        m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨hD601, h601⟩))))
    · omega
  · have hrange : 261 ≤ q4 ∧ q4 ≤ 264 := by
      rcases hDq4range with hr | hr | hr <;> omega
    have hqcase := OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_q4_candidate
      q4 hq4prime hrange.1 hrange.2
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
      m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h75, hqcase⟩)))))
  · have hrange : 146 ≤ q4 ∧ q4 ≤ 148 := by
      rcases hDq4range with hr | hr | hr <;> omega
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
      m a b c e D p q4 sigma hfac hsigma hrel hp_eq hb hc he
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h135, hq4prime, hrange.1, hrange.2⟩)))))

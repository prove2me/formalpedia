-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_absurd_v3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:24:09.462372+00:00
-- url     : https://prove2.me/submissions/322072b3-8895-4417-acdd-1338572a6e6a

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_le_43_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_31_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_37_canonical_absurd_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_absurd_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 29 < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) : False := by
  have hle43 :=
    OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_le_43_v5
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq
      hq4prime hq4gt ha hb hc he
  have hsplit : q4 = 30 ∨ q4 = 31 ∨ q4 = 32 ∨ q4 = 33 ∨ q4 = 34 ∨
      q4 = 35 ∨ q4 = 36 ∨ q4 = 37 ∨ q4 = 38 ∨ q4 = 39 ∨ q4 = 40 ∨
      q4 = 41 ∨ q4 = 42 ∨ q4 = 43 := by omega
  rcases hsplit with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst h; norm_num at hq4prime
  · subst h
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_31_absurd_v3
      m a b c e D p 31 sigma hfac hsigma hrel hDlow hp hp_eq rfl
      ha hb hc he
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_37_canonical_absurd_v2
      m a b c e D p 37 sigma hfac hsigma hrel hDlow hDodd hp hp_eq
      hq4prime rfl hDsupport ha hb hc he
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h; norm_num at hq4prime
  · subst h
    have hDupper :=
      OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_D_le_105_v3
        m a b c e D p 41 sigma hfac hsigma hrel hDlow hp hp_eq
        hq4prime rfl ha hb hc he
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_41_absurd_v4
      m a b c e D p 41 sigma hfac hsigma hrel hDlow hDupper hDodd hp
      hp_eq rfl hDsupport ha hb hc he
  · subst h; norm_num at hq4prime
  · subst h
    have hcase :=
      OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
        m a b c e D p 43 sigma hfac hsigma hrel hDlow hDodd hp hp_eq
        hq4prime rfl hDsupport ha hb hc he
    obtain ⟨hD75, hp149⟩ := hcase
    subst hD75
    subst hp149
    exact OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_absurd_v2
      m a b c e sigma hfac hsigma hrel hb

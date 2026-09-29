-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_case_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:13:29.258584+00:00
-- url     : https://prove2.me/submissions/5cbdaec5-fe49-4595-9d1c-1d731b8f2dbd

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 29 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ (i)) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ (i)) *
      (∑ i ∈ Finset.range (2*c + 1), 29 ^ (i)) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ (i)))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 75 ≤ D)
    (hDodd : Odd D) (hp : p.Prime) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4eq : q4 = 43)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 29 ∨ r = q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e) :
    D = 75 ∧ p = 149 := by
  have hDle := OddPerfectNumber.k_one_q2_five_q3_twentynine_large_D_q4_43_D_le_84_v2
    m a b c e D p q4 sigma hfac hsigma hrel hDlow hp hp_eq hq4prime hq4eq
    ha hb hc he
  rcases hDodd with ⟨k, hk⟩
  have hcases : D = 75 ∨ D = 77 ∨ D = 79 ∨ D = 81 ∨ D = 83 := by
    clear hfac hsigma hrel hp hp_eq hq4prime hq4eq hDsupport ha hb hc he
    omega
  rcases hcases with h75 | hrest
  · constructor
    · exact h75
    · omega
  rcases hrest with h77 | hrest
  · have hp' := hp
    rw [hp_eq, h77] at hp'
    norm_num at hp'
  rcases hrest with h79 | hrest
  · have hdiv : 79 ∣ D := by
      rw [h79]
    have hs := hDsupport 79 (by norm_num) hdiv
    norm_num [hq4eq] at hs
  rcases hrest with h81 | h83
  · have hp' := hp
    rw [hp_eq, h81] at hp'
    norm_num at hp'
  · have hp' := hp
    rw [hp_eq, h83] at hp'
    norm_num at hp'

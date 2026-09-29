-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_eq_two_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:42:41.765465+00:00
-- url     : https://prove2.me/submissions/1d46b4e5-755f-4b2e-bbfb-99be9ece9caa

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha2 : 2 ≤ a) (haeven : Even a) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 := by
  by_contra hne
  rcases haeven with ⟨k, hk⟩
  have ha4 : 4 ≤ a := by omega
  have hfalse := OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
    m a b c e q4 sigma hfac hsigma hupper ha4 hb hc
      (OddPerfectNumber.geom_sum_last_term_le q4 e)
  exact hfalse.elim

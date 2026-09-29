-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T02:34:50.994363+00:00
-- url     : https://prove2.me/submissions/4515900e-c959-414d-a099-cec9cd53198d

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v3
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_middle_D_canonical_dispatch_v2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_thirteen_large_D_absurd

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 13 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hp_eq : p = 2 * D - 1) (hq4 : q4.Prime)
    (hq4gt : 13 < q4) (hq4le : q4 ≤ 89) (hq4dvd : q4 ∣ D)
    (ha : 2 ≤ a) (hb : 8 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hDupper : D ≤ 685) (h5pow : 390625 ∣ D) :
    False := by
  by_cases hlow : D < 45
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_canonical_absurd_v3
      m a b c e D p q4 sigma hfac hsigma hrel hlow hp hp4 hp_eq hq4 hq4gt hq4dvd ha hb hc he
  have hmid : D < 214 ∨ 215 ≤ D := by
    by_cases h : D < 214
    · exact Or.inl h
    · have hge : 214 ≤ D := by omega
      rcases hDodd with ⟨k, hk⟩
      by_cases hEq : D = 214
      · omega
      · exact Or.inr (by omega)
  rcases hmid with hmid | hlarge
  · exact OddPerfectNumber.k_one_q2_five_q3_thirteen_middle_D_canonical_dispatch_v2
      m a b c e D p q4 sigma hfac hsigma hrel (by omega) hmid hp hp4 hp_eq hq4 hq4gt hq4le hq4dvd ha hb hc he
  exact OddPerfectNumber.k_one_q2_five_q3_thirteen_large_D_absurd D hlarge hDupper h5pow

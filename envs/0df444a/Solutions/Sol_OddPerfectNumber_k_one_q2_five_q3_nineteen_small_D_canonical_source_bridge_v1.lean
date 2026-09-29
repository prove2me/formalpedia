-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_canonical_source_bridge_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T03:05:03.444533+00:00
-- url     : https://prove2.me/submissions/00d266c4-f16e-4a85-a7cd-c26095f20f4c

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D57_source_dispatch
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D135_absurd

theorem solution
    (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hp_eq : p = 2 * D - 1)
    (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hcases :
      (D = 57 ∧ q4 = 587) ∨
      (D = 57 ∧ q4 = 593) ∨
      (D = 57 ∧ q4 = 599) ∨
      (D = 57 ∧ q4 = 601) ∨
      (D = 75 ∧ q4 = 263) ∨
      (D = 135 ∧ q4.Prime ∧ 146 ≤ q4 ∧ q4 ≤ 148)) :
    False := by
  rcases hcases with h | h | h | h | h | h
  · rcases h with ⟨rfl, rfl⟩
    have hp113 : p = 113 := by omega
    subst p
    have h113mul : 113 ∣ 57 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_left (dvd_refl 113) (m ^ 2)
    have h113sigma : 113 ∣ sigma := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 113)).mp h113mul with hbad | hs
      · norm_num at hbad
      · exact hs
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e 587 hsigma (Or.inl ⟨rfl, h113sigma⟩)
  · rcases h with ⟨rfl, rfl⟩
    have hpow : 593 ∣ 593 ^ (2 * e) := dvd_pow_self 593 (by omega)
    have hmdiv : 593 ∣ m ^ 2 := by
      rw [hfac]
      exact dvd_mul_of_dvd_right hpow _
    have hmuldiv : 593 ∣ 57 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_right hmdiv p
    have h593sigma : 593 ∣ sigma := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 593)).mp hmuldiv with hbad | hs
      · norm_num at hbad
      · exact hs
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e 593 hsigma (Or.inr (Or.inl ⟨rfl, h593sigma⟩))
  · rcases h with ⟨rfl, rfl⟩
    have hp113 : p = 113 := by omega
    subst p
    have h113mul : 113 ∣ 57 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_left (dvd_refl 113) (m ^ 2)
    have h113sigma : 113 ∣ sigma := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 113)).mp h113mul with hbad | hs
      · norm_num at hbad
      · exact hs
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e 599 hsigma (Or.inr (Or.inr (Or.inl ⟨rfl, h113sigma⟩)))
  · rcases h with ⟨rfl, rfl⟩
    have hp113 : p = 113 := by omega
    subst p
    have h113mul : 113 ∣ 57 * sigma := by
      rw [hrel]
      exact dvd_mul_of_dvd_left (dvd_refl 113) (m ^ 2)
    have h113sigma : 113 ∣ sigma := by
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 113)).mp h113mul with hbad | hs
      · norm_num at hbad
      · exact hs
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D57_source_dispatch
      sigma a b c e 601 hsigma (Or.inr (Or.inr (Or.inr ⟨rfl, h113sigma⟩)))
  · rcases h with ⟨rfl, rfl⟩
    have hp149 : p = 149 := by omega
    subst p
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D75_abundance_absurd_v5
      m a b c e sigma hfac hsigma hrel hb hc he
  · rcases h with ⟨rfl, hq4prime, hlow, hhigh⟩
    exact OddPerfectNumber.k_one_q2_five_q3_nineteen_D135_absurd
      q4 hq4prime hlow hhigh

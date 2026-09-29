-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_case_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T20:59:28.458981+00:00
-- url     : https://prove2.me/submissions/b9124713-ba4f-4be4-bd85-da17ff9abc02

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_D_factor_support_form_v4
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_q4_six_cases
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_97_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_101_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_103_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_107_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_109_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_q4_113_window
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlow : 225 ≤ D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 19 < q4) (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c)
    (he : 1 ≤ e)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 19 ∨ r = q4) :
    D = 855 ∧ q4 = 101 ∧ p = 1709 := by
  have hDdvd :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_D_dvd_m2
      m D p sigma hrel hp hp_eq
  have hform0 :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_D_factor_support_form_v4
      m a b c e D q4 hfac hDdvd (by omega) hq4prime hq4gt hDsupport
  rcases hform0 with ⟨i, j, k, l, hform, hi0, hj0, hk0, hl0⟩
  have hcases :=
    OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_six_cases
      m a b c e D p q4 sigma hfac hsigma hrel hDlow hp_eq hq4prime hq4gt
      ha hb hc he
  have hwin :
      (q4 = 97 ∧ 2881 ≤ D ∧ D ≤ 4608) ∨
      (q4 = 101 ∧ 854 ≤ D ∧ D ≤ 960) ∨
      (q4 = 103 ∧ 642 ≤ D ∧ D ≤ 699) ∨
      (q4 = 107 ∧ 437 ≤ D ∧ D ≤ 462) ∨
      (q4 = 109 ∧ 379 ≤ D ∧ D ≤ 398) ∨
      (q4 = 113 ∧ 304 ≤ D ∧ D ≤ 316) := by
    rcases hcases with h97 | h101 | h103 | h107 | h109 | h113
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_97_window
        m a b c e D p 97 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inl ⟨rfl, hw.1, hw.2⟩
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_101_window
        m a b c e D p 101 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inr (Or.inl ⟨rfl, hw.1, hw.2⟩)
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_103_window
        m a b c e D p 103 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inr (Or.inr (Or.inl ⟨rfl, hw.1, hw.2⟩))
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_107_window
        m a b c e D p 107 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hw.1, hw.2⟩)))
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_109_window
        m a b c e D p 109 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hw.1, hw.2⟩))))
    · subst q4
      have hw := OddPerfectNumber.k_one_q2_five_q3_nineteen_q4_113_window
        m a b c e D p 113 sigma hfac hsigma hrel hDlow hp_eq rfl ha hb hc he
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hw.1, hw.2⟩))))
  have hDupper : D ≤ 4608 := by
    rcases hwin with h | h | h | h | h | h <;> omega
  have hq4ge : 97 ≤ q4 := by
    rcases hcases with h | h | h | h | h | h <;> omega
  have hq4two : 2 ≤ q4 := hq4prime.two_le
  have hq4pos : 0 < q4 := by omega
  have hi : i ≤ 7 := by
    by_contra hn
    have hge : 8 ≤ i := by omega
    have hpow : 6561 ≤ 3^i := by
      calc 6561 = 3^8 := by norm_num
        _ ≤ 3^i := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 3^i ≤ D := by
      rw [hform]
      have hpos : 0 < 5^j * 19^k * q4^l := by positivity
      simpa [Nat.mul_assoc] using Nat.le_mul_of_pos_right (3^i) hpos
    omega
  have hj : j ≤ 5 := by
    by_contra hn
    have hge : 6 ≤ j := by omega
    have hpow : 15625 ≤ 5^j := by
      calc 15625 = 5^6 := by norm_num
        _ ≤ 5^j := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 5^j ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 19^k * q4^l := by positivity
      have hbase : 5^j ≤ 5^j * (3^i * 19^k * q4^l) :=
        Nat.le_mul_of_pos_right (5^j) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  have hk : k ≤ 2 := by
    by_contra hn
    have hge : 3 ≤ k := by omega
    have hpow : 6859 ≤ 19^k := by
      calc 6859 = 19^3 := by norm_num
        _ ≤ 19^k := Nat.pow_le_pow_right (by norm_num) hge
    have hle : 19^k ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 5^j * q4^l := by positivity
      have hbase : 19^k ≤ 19^k * (3^i * 5^j * q4^l) :=
        Nat.le_mul_of_pos_right (19^k) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  have hl : l ≤ 1 := by
    by_contra hn
    have hge : 2 ≤ l := by omega
    have hpow : 9409 ≤ q4^l := by
      calc 9409 = 97^2 := by norm_num
        _ ≤ q4^2 := Nat.pow_le_pow_left hq4ge 2
        _ ≤ q4^l := Nat.pow_le_pow_right hq4pos hge
    have hle : q4^l ≤ D := by
      rw [hform]
      have hpos : 0 < 3^i * 5^j * 19^k := by positivity
      have hbase : q4^l ≤ q4^l * (3^i * 5^j * 19^k) :=
        Nat.le_mul_of_pos_right (q4^l) hpos
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
    omega
  exact OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_tuple_from_factor_support
    D p q4 i j k l hp hp_eq hcases hform hi hj hk hl hwin

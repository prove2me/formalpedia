-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_small_D_abundance_cut
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T11:28:26.791872+00:00
-- url     : https://prove2.me/submissions/2a9ffec9-f2c5-413c-a222-91ea12580dfb

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45 ∨ D = 57 ∨ D = 75 ∨ D = 135)
    (hp : p = 2 * D - 1)
    (hq4prime : q4.Prime)
    (ha : 8 ≤ a) (hb : 6 ≤ b) (hc : 4 ≤ c) (he : 2 ≤ e) :
    D = 57 ∨ D = 75 ∨ D = 135 := by
  let S3 := ∑ i ∈ Finset.range (a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (c + 1), 19 ^ i
  let Sq4 := ∑ i ∈ Finset.range (e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight a ha
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six b hb
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four c hc
  have hq4 := OddPerfectNumber.geom_sum_last_term_le q4 e
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q4 := Nat.mul_le_mul h19 hq4
  have hmul := Nat.mul_le_mul hmul35 hmul19q4
  have hcross :
      5287699850706 * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e) ≤
        2671987753125 * (S3 * S5 * S19 * Sq4) := by
    calc
      5287699850706 * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e) =
          (9841 * 3 ^ a) * (3906 * 5 ^ b) *
            ((137561 * 19 ^ c) * q4 ^ e) := by ring
      _ ≤ (6561 * S3) * (3125 * S5) * ((130321 * S19) * Sq4) := by
        simpa only [S3, S5, S19, Sq4] using hmul
      _ = 2671987753125 * (S3 * S5 * S19 * Sq4) := by ring
  have hq4pos : 0 < q4 := hq4prime.pos
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) a)
      (pow_pos (by norm_num) b)) (pow_pos (by norm_num) c)) (pow_pos hq4pos e)
  have hineq : 5287699850706 * D * (m ^ 2) ≤ 2671987753125 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    have hraw :
        5287699850706 * D * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e) ≤
          2671987753125 * D * (S3 * S5 * S19 * Sq4) := by
      calc
        5287699850706 * D * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e) =
            D * (5287699850706 * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e)) := by ring
        _ ≤ D * (2671987753125 * (S3 * S5 * S19 * Sq4)) := hmulD
        _ = 2671987753125 * D * (S3 * S5 * S19 * Sq4) := by ring
    calc
      5287699850706 * D * (m ^ 2) =
          5287699850706 * D * (3 ^ a * 5 ^ b * 19 ^ c * q4 ^ e) := by rw [hfac]
      _ ≤ 2671987753125 * D * (S3 * S5 * S19 * Sq4) := hraw
      _ = 2671987753125 * D * sigma := by rw [hsigma]
      _ = 2671987753125 * (D * sigma) := by ring
      _ = 2671987753125 * (p * (m ^ 2)) := by rw [hrel]
      _ = 2671987753125 * p * (m ^ 2) := by ring
  rcases hDcases with h | h | h | h | h | h | h | h | h <;> subst D <;> norm_num at hp
  · have hconst : 2671987753125 * p < 5287699850706 * 3 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 3 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · have hconst : 2671987753125 * p < 5287699850706 * 9 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 9 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · have hconst : 2671987753125 * p < 5287699850706 * 15 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 15 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · have hconst : 2671987753125 * p < 5287699850706 * 19 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 19 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · have hconst : 2671987753125 * p < 5287699850706 * 27 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 27 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · have hconst : 2671987753125 * p < 5287699850706 * 45 := by norm_num [hp]
    have hstrict : 2671987753125 * p * (m ^ 2) < 5287699850706 * 45 * (m ^ 2) := by
      exact Nat.mul_lt_mul_of_pos_right hconst hmpos
    exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_abundance_cut_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T21:12:02.848566+00:00
-- url     : https://prove2.me/submissions/16542490-7cbb-44aa-8170-627968a3c8a4

import Mathlib
import Theorems.Thm_OddPerfectNumber_k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_ten
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2) (hDlt : D < 111) (hDodd : Odd D)
    (hp : p.Prime) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime)
    (hq4gt : 23 < q4) (hDq : D < q4)
    (hDsupport : ∀ r, r.Prime → r ∣ D →
      r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4)
    (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) :
    D = 27 ∨ D = 45 ∨ D = 69 ∨ D = 75 := by
  have hcases := OddPerfectNumber.k_one_q2_five_q3_twentythree_D_lt_111_support_cases_v5
    D p q4 hDlt hDodd hp hp_eq hq4gt hDq hDsupport
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S23 : Nat := ∑ i ∈ Finset.range (2*c + 1), 23 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_ten (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have hgeom := OddPerfectNumber.geom_mul_sub_one 23 (2*c + 1) (by norm_num)
  rw [pow_succ] at hgeom
  have hpow23 : 23 ^ 8 ≤ 23 ^ (2*c) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < 23) (by omega)
  have h23 : 81870575521 * 23 ^ (2*c) ≤
      78310985281 * S23 := by
    dsimp [S23]
    omega
  have hq := OddPerfectNumber.geom_sum_last_term_le q4 (2*e)
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) (Nat.mul_le_mul h23 hq)
  have hcross :
      141629485666674161023 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) ≤
        72252896404027640625 * (S3 * S5 * S23 * Sq) := by
    calc
      141629485666674161023 *
          (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) =
          (88573 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((81870575521 * 23^(2*c)) * (q4^(2*e))) := by ring
      _ ≤ (59049 * S3) * (15625 * S5) *
            ((78310985281 * S23) * Sq) := by
        simpa only [S3, S5, S23, Sq] using hmul
      _ = 72252896404027640625 * (S3 * S5 * S23 * Sq) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hineq :
      141629485666674161023 * D * (m ^ 2) ≤
        72252896404027640625 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      141629485666674161023 * D * (m ^ 2) =
          D * (141629485666674161023 *
            (3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e))) := by
              rw [hfac]
              ring
      _ ≤ D * (72252896404027640625 * (S3 * S5 * S23 * Sq)) := hmulD
      _ = 72252896404027640625 * (D * sigma) := by rw [hsigma]; ring
      _ = 72252896404027640625 * (p * (m ^ 2)) := by rw [hrel]
      _ = 72252896404027640625 * p * (m ^ 2) := by ring
  have hnot3 : D ≠ 3 := by
    intro hD3
    have hp3 : p = 5 := by omega
    have hrev : 72252896404027640625 * p * (m^2) <
        141629485666674161023 * D * (m^2) := by
      have hc3 : 72252896404027640625 * 5 < 141629485666674161023 * 3 := by norm_num
      simpa [hD3, hp3] using Nat.mul_lt_mul_of_pos_right hc3 hmpos
    exact (Nat.not_lt_of_ge hineq) hrev
  have hnot9 : D ≠ 9 := by
    intro hD9
    have hp9 : p = 17 := by omega
    have hrev : 72252896404027640625 * p * (m^2) <
        141629485666674161023 * D * (m^2) := by
      have hc9 : 72252896404027640625 * 17 < 141629485666674161023 * 9 := by norm_num
      simpa [hD9, hp9] using Nat.mul_lt_mul_of_pos_right hc9 hmpos
    exact (Nat.not_lt_of_ge hineq) hrev
  have hnot15 : D ≠ 15 := by
    intro hD15
    have hp15 : p = 29 := by omega
    have hrev : 72252896404027640625 * p * (m^2) <
        141629485666674161023 * D * (m^2) := by
      have hc15 : 72252896404027640625 * 29 < 141629485666674161023 * 15 := by norm_num
      simpa [hD15, hp15] using Nat.mul_lt_mul_of_pos_right hc15 hmpos
    exact (Nat.not_lt_of_ge hineq) hrev
  rcases hcases with h3 | h9 | h15 | h27 | h45 | h69 | h75
  · exact False.elim (hnot3 h3)
  · exact False.elim (hnot9 h9)
  · exact False.elim (hnot15 h15)
  · exact Or.inl h27
  · exact Or.inr (Or.inl h45)
  · exact Or.inr (Or.inr (Or.inl h69))
  · exact Or.inr (Or.inr (Or.inr h75))

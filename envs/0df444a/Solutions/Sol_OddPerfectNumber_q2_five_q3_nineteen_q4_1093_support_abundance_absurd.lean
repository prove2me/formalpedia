-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_1093_support_abundance_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:39:06.725883+00:00
-- url     : https://prove2.me/submissions/887f8db0-a2da-4486-9a7e-560214a12c65

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_two
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution (m b c e D p sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (6 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 1093 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDcases : D = 3 ∨ D = 9 ∨ D = 15 ∨ D = 19 ∨ D = 27 ∨ D = 45)
    (hp : p = 2 * D - 1)
    (hb : 6 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  let S3 := ∑ i ∈ Finset.range (6 + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (c + 1), 19 ^ i
  let S1093 := ∑ i ∈ Finset.range (e + 1), 1093 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_six 6 (by norm_num)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six b hb
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_two c hc
  have h1093 := OddPerfectNumber.geom_sum_last_term_le 1093 e
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul191093 := Nat.mul_le_mul h19 h1093
  have hmul := Nat.mul_le_mul hmul35 hmul191093
  have hcross :
      1626587298 * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e) ≤
        822403125 * (S3 * S5 * S19 * S1093) := by
    calc
      1626587298 * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e) =
          (1093 * 3 ^ 6) * (3906 * 5 ^ b) *
            ((381 * 19 ^ c) * 1093 ^ e) := by ring
      _ ≤ (729 * S3) * (3125 * S5) * ((361 * S19) * S1093) := by
        simpa only [S3, S5, S19, S1093] using hmul
      _ = 822403125 * (S3 * S5 * S19 * S1093) := by ring
  have hconst : 822403125 * p < 1626587298 * D := by
    rcases hDcases with h3D | h9D | h15D | h19D | h27D | h45D <;>
      subst D
    all_goals
      norm_num at hp
      norm_num [hp]
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hineq : 1626587298 * D * (m ^ 2) ≤ 822403125 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    have hraw :
        1626587298 * D * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e) ≤
          822403125 * D * (S3 * S5 * S19 * S1093) := by
      calc
        1626587298 * D * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e) =
            D * (1626587298 * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e)) := by ring
        _ ≤ D * (822403125 * (S3 * S5 * S19 * S1093)) := hmulD
        _ = 822403125 * D * (S3 * S5 * S19 * S1093) := by ring
    calc
      1626587298 * D * (m ^ 2) =
          1626587298 * D * (3 ^ 6 * 5 ^ b * 19 ^ c * 1093 ^ e) := by rw [hfac]
      _ ≤ 822403125 * D * (S3 * S5 * S19 * S1093) := hraw
      _ = 822403125 * D * sigma := by rw [hsigma]
      _ = 822403125 * (D * sigma) := by ring
      _ = 822403125 * (p * (m ^ 2)) := by rw [hrel]
      _ = 822403125 * p * (m ^ 2) := by ring
  have hstrict : 822403125 * p * (m ^ 2) < 1626587298 * D * (m ^ 2) := by
    exact Nat.mul_lt_mul_of_pos_right hconst hmpos
  exact (Nat.not_lt_of_ge hineq) hstrict

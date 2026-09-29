-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_large_D_q4_gt_89
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T14:33:52.031321+00:00
-- url     : https://prove2.me/submissions/ef6e96c7-56c9-4887-8c2b-a117df51b99c

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_eight
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_six_sharp
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_nineteen_ge_four
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hDlow : 225 ≤ D) (hp_eq : p = 2 * D - 1)
    (hq4prime : q4.Prime) (hq4gt : 19 < q4)
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hq4le : q4 ≤ 89) :
    False := by
  let S3 : Nat := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 : Nat := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 : Nat := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq : Nat := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_eight (2*a) (by omega)
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_six_sharp (2*b) (by omega)
  have h19 := OddPerfectNumber.geom_ratio_lower_nineteen_ge_four (2*c) (by omega)
  have hlast := OddPerfectNumber.geom_sum_last_two_terms_le q4 (2*e) (by omega)
  have hpow : q4 ^ (2*e) ≤ 89 * q4 ^ (2*e - 1) := by
    rw [show 2*e = (2*e - 1) + 1 by omega, pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (q4 ^ (2*e - 1)) hq4le
  have hlin : 90 * q4 ^ (2*e) ≤
      89 * q4 ^ (2*e) + 89 * q4 ^ (2*e - 1) := by omega
  have hq : 90 * q4 ^ (2*e) ≤ 89 * Sq := by
    calc
      90 * q4 ^ (2*e) ≤ 89 * q4 ^ (2*e) + 89 * q4 ^ (2*e - 1) := hlin
      _ = 89 * (q4 ^ (2*e) + q4 ^ (2*e - 1)) := by ring
      _ ≤ 89 * Sq := Nat.mul_le_mul_left 89 (by simpa [Sq] using hlast)
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul19q := Nat.mul_le_mul h19 hq
  have hmul := Nat.mul_le_mul hmul35 hmul19q
  have hcross :
      2379586769219790 * (3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) ≤
        1189034550140625 * (S3 * S5 * S19 * Sq) := by
    calc
      2379586769219790 * (3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e)) =
          (9841 * 3^(2*a)) * (19531 * 5^(2*b)) *
            ((137561 * 19^(2*c)) * (90 * q4^(2*e))) := by ring
      _ ≤ (6561 * S3) * (15625 * S5) *
            ((130321 * S19) * (89 * Sq)) := by
        simpa only [S3, S5, S19, Sq] using hmul
      _ = 1189034550140625 * (S3 * S5 * S19 * Sq) := by ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  have hineq :
      2379586769219790 * D * (m ^ 2) ≤
        1189034550140625 * p * (m ^ 2) := by
    have hmulD := Nat.mul_le_mul_left D hcross
    calc
      2379586769219790 * D * (m ^ 2) =
          D * (2379586769219790 * (3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))) := by rw [hfac]; ring
      _ ≤ D * (1189034550140625 * (S3 * S5 * S19 * Sq)) := hmulD
      _ = 1189034550140625 * (D * sigma) := by rw [hsigma]; ring
      _ = 1189034550140625 * (p * (m ^ 2)) := by rw [hrel]
      _ = 1189034550140625 * p * (m ^ 2) := by ring
  have hconst : 2 * 1189034550140625 < 2379586769219790 := by norm_num
  have hp_lt : p < 2 * D := by omega
  have hstrict :
      1189034550140625 * p * (m ^ 2) <
        2379586769219790 * D * (m ^ 2) := by
    have hmulP := Nat.mul_lt_mul_of_pos_right hp_lt hmpos
    have hcoef : 1189034550140625 * p <
        2 * 1189034550140625 * D := by
      calc
        1189034550140625 * p <
            1189034550140625 * (2 * D) :=
          Nat.mul_lt_mul_of_pos_left hp_lt (by norm_num)
        _ = 2 * 1189034550140625 * D := by ring
    have hcoef' : 1189034550140625 * p <
        2379586769219790 * D := lt_of_lt_of_le hcoef (by
          exact Nat.mul_le_mul_right D (Nat.le_of_lt hconst))
    exact Nat.mul_lt_mul_of_pos_right hcoef' hmpos
  exact False.elim ((Nat.not_lt_of_ge hineq) hstrict)

-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_exp3_ge_four_abundance_absurd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T02:54:01.148271+00:00
-- url     : https://prove2.me/submissions/1575cb42-577b-4641-b0ca-24eb81c284c3

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_four
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

theorem solution (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 13 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 13 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (ha : 4 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (hq : q4 ^ e ≤ ∑ i ∈ Finset.range (e + 1), q4 ^ i) :
    False := by
  let S3 := ∑ i ∈ Finset.range (a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i
  let S13 := ∑ i ∈ Finset.range (c + 1), 13 ^ i
  let Sq := ∑ i ∈ Finset.range (e + 1), q4 ^ i
  let P := 3 ^ a * 5 ^ b * 13 ^ c
  let S := S3 * S5 * S13
  have sum_pos : ∀ q n : Nat,
      0 < ∑ i ∈ Finset.range (n + 1), q ^ i := by
    intro q n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show Nat.succ n + 1 = (n + 1) + 1 by omega,
          Finset.sum_range_succ]
        omega
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_four a ha
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_two b hb
  have h13 := OddPerfectNumber.geom_ratio_lower_thirteen_ge_two c hc
  have hmul35 := Nat.mul_le_mul h3 h5
  have hmul := Nat.mul_le_mul hmul35 h13
  have hcross :
      (121 * 31 * 183) * P ≤
        (81 * 25 * 169) * S := by
    simpa [P, S, S3, S5, S13, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hconst :
      2 * (81 * 25 * 169) < 121 * 31 * 183 := by
    norm_num
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hqpowpos : 0 < q4 ^ e := by
    by_contra hzero
    have hqpowzero : q4 ^ e = 0 := Nat.eq_zero_of_not_pos hzero
    have hmzero : m ^ 2 = 0 := by
      simpa [P, hqpowzero] using hfac
    have hsigma_zero : sigma = 0 := by
      omega
    have hS3pos : 0 < S3 := sum_pos 3 a
    have hS5pos : 0 < S5 := sum_pos 5 b
    have hS13pos : 0 < S13 := sum_pos 13 c
    have hSqpos : 0 < Sq := sum_pos q4 e
    have hsigma_pos : 0 < sigma := by
      rw [hsigma]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hS3pos hS5pos) hS13pos) hSqpos
    omega
  have hstrict :
      (2 * (81 * 25 * 169)) * P <
        ((121 * 31 * 183)) * P :=
    Nat.mul_lt_mul_of_pos_right hconst hPpos
  have hchain :
      (81 * 25 * 169) * (2 * (P * q4 ^ e)) <
        (81 * 25 * 169) * (S * Sq) := by
    have hmulq := Nat.mul_le_mul hcross hq
    calc
      (81 * 25 * 169) * (2 * (P * q4 ^ e)) =
          (2 * (81 * 25 * 169)) * (P * q4 ^ e) := by ring
      _ < (121 * 31 * 183) * (P * q4 ^ e) := by
        exact Nat.mul_lt_mul_of_pos_right hconst
          (Nat.mul_pos hPpos hqpowpos)
      _ ≤ ((81 * 25 * 169) * S) * Sq := by
        calc
          (121 * 31 * 183) * (P * q4 ^ e) =
              ((121 * 31 * 183) * P) * q4 ^ e := by ring
          _ ≤ ((81 * 25 * 169) * S) * Sq := by
            exact Nat.mul_le_mul hcross hq
      _ = (81 * 25 * 169) * (S * Sq) := by ring
  have hdenpos : 0 < 81 * 25 * 169 := by norm_num
  have hfinal : 2 * (P * q4 ^ e) < S * Sq :=
    (Nat.mul_lt_mul_left hdenpos).1 hchain
  have hsig_gt : 2 * m ^ 2 < sigma := by
    simpa [hfac, hsigma, P, S, S3, S5, S13, Sq,
      mul_assoc, mul_left_comm, mul_comm] using hfinal
  omega

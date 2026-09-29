-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_exp3_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:52:43.847682+00:00
-- url     : https://prove2.me/submissions/cfbc8adc-d81c-41f4-9bb9-51f2cf614a0c

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_three_ge_four
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_eleven_ge_two_sharp_v3
import Theorems.Thm_OddPerfectNumber_geom_sum_last_term_le

theorem solution
    (m a b c e q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ a * 5 ^ b * 11 ^ c * q4 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), q4 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hq4prime : q4.Prime) (ha2 : 2 ≤ a) (haeven : Even a)
    (hb : 2 ≤ b) (hc : 2 ≤ c) :
    a = 2 := by
  by_contra hne
  rcases haeven with ⟨k, hk⟩
  have ha4 : 4 ≤ a := by omega
  let S3 := ∑ i ∈ Finset.range (a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i
  let S11 := ∑ i ∈ Finset.range (c + 1), 11 ^ i
  let Sq := ∑ i ∈ Finset.range (e + 1), q4 ^ i
  let P := 3 ^ a * 5 ^ b * 11 ^ c
  let S := S3 * S5 * S11
  have h3 := OddPerfectNumber.geom_ratio_lower_three_ge_four a ha4
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_two b hb
  have h11 := OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp_v3 c hc
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h11
  have hcross : (121 * 31 * 133) * P ≤ (81 * 25 * 121) * S := by
    simpa [P, S, S3, S5, S11, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hq := OddPerfectNumber.geom_sum_last_term_le q4 e
  have hconst : 2 * (81 * 25 * 121) < 121 * 31 * 133 := by norm_num
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hqpowpos : 0 < q4 ^ e := pow_pos hq4prime.pos _
  have hchain :
      (81 * 25 * 121) * (2 * (P * q4 ^ e)) <
        (81 * 25 * 121) * (S * Sq) := by
    have hmulq := Nat.mul_le_mul hcross hq
    calc
      (81 * 25 * 121) * (2 * (P * q4 ^ e)) =
          (2 * (81 * 25 * 121)) * (P * q4 ^ e) := by ring
      _ < (121 * 31 * 133) * (P * q4 ^ e) := by
        exact Nat.mul_lt_mul_of_pos_right hconst
          (Nat.mul_pos hPpos hqpowpos)
      _ ≤ ((81 * 25 * 121) * S) * Sq := by
        calc
          (121 * 31 * 133) * (P * q4 ^ e) =
              ((121 * 31 * 133) * P) * q4 ^ e := by ring
          _ ≤ ((81 * 25 * 121) * S) * Sq := by
            exact Nat.mul_le_mul hcross hq
      _ = (81 * 25 * 121) * (S * Sq) := by ring
  have hdenpos : 0 < 81 * 25 * 121 := by norm_num
  have hfinal : 2 * (P * q4 ^ e) < S * Sq :=
    (Nat.mul_lt_mul_left hdenpos).1 hchain
  have hgt : 2 * m ^ 2 < sigma := by
    simpa [hfac, hsigma, P, S, S3, S5, S11, Sq,
      mul_assoc, mul_left_comm, mul_comm] using hfinal
  omega

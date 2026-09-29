-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_eleven_q4_13_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T22:39:30.904323+00:00
-- url     : https://prove2.me/submissions/0c00cca3-625c-445c-9b29-7b154264fe24

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_five_ge_two
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_eleven_ge_two_sharp_v3
import Theorems.Thm_OddPerfectNumber_geom_ratio_lower_thirteen_ge_two

theorem solution
    (m b c e sigma : Nat)
    (hfac : m ^ 2 = 3 ^ 2 * 5 ^ b * 11 ^ c * 13 ^ e)
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2 + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (c + 1), 11 ^ i) *
      (∑ i ∈ Finset.range (e + 1), 13 ^ i))
    (hupper : sigma ≤ 2 * m ^ 2)
    (hb : 2 ≤ b) (hc : 2 ≤ c) (he : 2 ≤ e) :
    False := by
  let S5 := ∑ i ∈ Finset.range (b + 1), 5 ^ i
  let S11 := ∑ i ∈ Finset.range (c + 1), 11 ^ i
  let S13 := ∑ i ∈ Finset.range (e + 1), 13 ^ i
  let P := 5 ^ b * 11 ^ c * 13 ^ e
  let S := S5 * S11 * S13
  have h5 := OddPerfectNumber.geom_ratio_lower_five_ge_two b hb
  have h11 := OddPerfectNumber.geom_ratio_lower_eleven_ge_two_sharp_v3 c hc
  have h13 := OddPerfectNumber.geom_ratio_lower_thirteen_ge_two e he
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul h5 h11) h13
  have hcross : (31 * 133 * 183) * P ≤ (25 * 121 * 169) * S := by
    simpa [P, S, S5, S11, S13, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hconst : 18 * (25 * 121 * 169) < 13 * (31 * 133 * 183) := by
    norm_num
  have hPpos : 0 < P := by
    dsimp [P]
    positivity
  have hchain :
      (25 * 121 * 169) * (18 * P) <
        (25 * 121 * 169) * (13 * S) := by
    calc
      (25 * 121 * 169) * (18 * P) =
          (18 * (25 * 121 * 169)) * P := by ring
      _ < (13 * (31 * 133 * 183)) * P := by
        exact Nat.mul_lt_mul_of_pos_right hconst hPpos
      _ ≤ (13 * (25 * 121 * 169)) * S := by
        calc
          (13 * (31 * 133 * 183)) * P =
              13 * ((31 * 133 * 183) * P) := by ring
          _ ≤ 13 * ((25 * 121 * 169) * S) :=
            Nat.mul_le_mul_left 13 hcross
          _ = (13 * (25 * 121 * 169)) * S := by ring
      _ = (25 * 121 * 169) * (13 * S) := by ring
  have hBpos : 0 < 25 * 121 * 169 := by norm_num
  have hfinal : 18 * P < 13 * S :=
    (Nat.mul_lt_mul_left hBpos).1 hchain
  have hm2 : m ^ 2 = 9 * P := by
    rw [hfac]
    norm_num [P]
    ring
  have hs : sigma = 13 * S := by
    rw [hsigma]
    norm_num [S, S5, S11, S13]
    ring
  have hgt : 2 * m ^ 2 < sigma := by
    calc
      2 * m ^ 2 = 18 * P := by rw [hm2]; ring
      _ < 13 * S := hfinal
      _ = sigma := hs.symm
  omega

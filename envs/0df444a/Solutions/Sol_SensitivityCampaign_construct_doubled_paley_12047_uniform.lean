-- Prove2me | solution 1 for SensitivityCampaign.construct_doubled_paley_12047_uniform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T04:55:53.217024+00:00
-- url     : https://prove2.me/submissions/3654d028-57ff-4553-b805-077526f3c774

import Mathlib
import Definitions.Def_SensitivityCampaign
import Definitions.Def_BS2_b3ba934b_Endpoint16Seeds
import Theorems.Thm_SensitivityPublishing213519_periodic_upper

open OAI.Paper320

theorem solution :
  ∃ C : ℕ, 0 < C ∧ ∀ k : ℕ,
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      2 ^ (8*k) ≤ sensitivity f ∧
      sensitivity f ≤ C * 2084175267334724 ^ k ∧
      12047 ^ (8*k) ≤ blockSensitivity f := by
  have hseeds := ThreeBoundEndpoint16Seeds.seeds_of_periodic_upper SensitivityPublishing213519.periodic_upper
  refine ⟨ThreeBoundEndpoint16Seeds.prefactor * 31192129, by
    have := ThreeBoundEndpoint16Seeds.prefactor_gt_one; positivity, fun k => ?_⟩
  set m := (49 * k + 23) / 24 with hm
  have hm1 : 2 * k ≤ m := by rw [hm, Nat.le_div_iff_mul_le (by norm_num)]; omega
  have hm2 : 24 * m ≤ 49 * k + 23 := by rw [hm]; have := Nat.div_mul_le_self (49 * k + 23) 24; omega
  have hm3 : 49 * k ≤ 24 * m := by rw [hm]; have := Nat.lt_div_mul_add (a := 49 * k + 23) (b := 24) (by norm_num); omega
  obtain ⟨n, f, h1, h2, h3⟩ := hseeds m
  refine ⟨n, f, ?_, ?_, ?_⟩
  · refine le_trans ?_ h1
    calc 2 ^ (8 * k) = 16 ^ (2 * k) := by rw [show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_mul]; ring_nf
      _ ≤ 16 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  · refine le_trans h2 ?_
    rw [mul_assoc]
    apply Nat.mul_le_mul_left
    have hA : (31192129 : ℕ) ^ 49 ≤ 2084175267334724 ^ 24 := by norm_num
    have : (31192129 ^ m) ^ 24 ≤ (31192129 * 2084175267334724 ^ k) ^ 24 := by
      calc (31192129 ^ m) ^ 24 = 31192129 ^ (24 * m) := by rw [← pow_mul, mul_comm]
        _ ≤ 31192129 ^ (49 * k + 24) := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 31192129 ^ 24 * (31192129 ^ 49) ^ k := by rw [← pow_mul, ← pow_add]; ring_nf
        _ ≤ 31192129 ^ 24 * (2084175267334724 ^ 24) ^ k :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA k)
        _ = (31192129 * 2084175267334724 ^ k) ^ 24 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 24 k]
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this
  · refine le_trans ?_ h3
    have hB : (12047 : ℕ) ^ 192 ≤ (10007 ^ 4) ^ 49 := by norm_num
    have : (12047 ^ (8 * k)) ^ 24 ≤ ((10007 ^ 4) ^ m) ^ 24 := by
      calc (12047 ^ (8 * k)) ^ 24 = (12047 ^ 192) ^ k := by rw [← pow_mul, ← pow_mul]; ring_nf
        _ ≤ ((10007 ^ 4) ^ 49) ^ k := Nat.pow_le_pow_left hB k
        _ = (10007 ^ 4) ^ (49 * k) := by rw [← pow_mul]
        _ ≤ (10007 ^ 4) ^ (24 * m) := Nat.pow_le_pow_right (by norm_num) hm3
        _ = ((10007 ^ 4) ^ m) ^ 24 := by rw [← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp this

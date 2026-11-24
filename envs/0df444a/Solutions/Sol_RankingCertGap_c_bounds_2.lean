-- Prove2me | solution 2 for RankingCertGap.c_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T23:02:53.963136+00:00
-- url     : https://prove2.me/submissions/b76754c0-c688-4f36-9126-fff500ad4548

import Mathlib
import Definitions.Def_RankingCertGap_SafetyState

set_option autoImplicit false

open RankingCertGap

private lemma cb_le_geom (k : ℕ) : (1 / 2 : ℝ) ^ (2 ^ (k + 1) + k) ≤ (1 / 2 : ℝ) ^ k :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left _ _)

private lemma cb_summable : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (2 ^ (k + 1) + k)) :=
  Summable.of_nonneg_of_le (fun k => by positivity) cb_le_geom
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

private lemma cb_tail_le (k : ℕ) :
    (1 / 2 : ℝ) ^ (2 ^ (k + 4 + 1) + (k + 4)) ≤ (1 / 2 : ℝ) ^ 36 * (1 / 2 : ℝ) ^ k := by
  rw [← pow_add]
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  have : 32 ≤ 2 ^ (k + 4 + 1) := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (k + 4 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

private lemma cb_split :
    (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 ^ (k + 1) + k)) =
      289 / 1024 + (1 / 2 : ℝ) ^ 19 + ∑' k : ℕ, (1 / 2 : ℝ) ^ (2 ^ (k + 4 + 1) + (k + 4)) := by
  rw [← cb_summable.sum_add_tsum_nat_add 4]
  simp [Finset.sum_range_succ]
  norm_num

private lemma cb_tail_bounds :
    0 ≤ (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 ^ (k + 4 + 1) + (k + 4))) ∧
      (∑' k : ℕ, (1 / 2 : ℝ) ^ (2 ^ (k + 4 + 1) + (k + 4))) ≤ (1 / 2 : ℝ) ^ 35 := by
  have hg : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ 36 * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hs : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (2 ^ (k + 4 + 1) + (k + 4))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) cb_tail_le hg
  refine ⟨tsum_nonneg (fun k => by positivity), ?_⟩
  calc _ ≤ ∑' k : ℕ, (1 / 2 : ℝ) ^ 36 * (1 / 2 : ℝ) ^ k := hs.tsum_le_tsum cb_tail_le hg
    _ = (1 / 2 : ℝ) ^ 35 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

theorem solution : (71777 : ℝ) / 100000 < cStar ∧ cStar < 359 / 500 := by
  unfold cStar
  rw [cb_split]
  obtain ⟨h0, h1⟩ := cb_tail_bounds
  constructor
  · norm_num at h1 ⊢; linarith
  · norm_num at h0 ⊢; linarith

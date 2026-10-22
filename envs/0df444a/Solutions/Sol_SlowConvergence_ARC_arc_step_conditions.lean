-- Prove2me | solution 1 for SlowConvergence.ARC.arc_step_conditions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:16:58.872973+00:00
-- url     : https://prove2.me/submissions/ebb64fe6-7f2c-44f2-84eb-974562db2795

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data

set_option autoImplicit false
open SlowConvergence.ARC

lemma S_eta_pos {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) : 0 < eta τ := by
  unfold eta
  have h3 : 0 < 3 - 2 * τ := by linarith
  have : 2 / 3 < 2 / (3 - 2 * τ) := div_lt_div_of_pos_left (by norm_num) h3 (by linarith)
  linarith

lemma S_sk_pos (τ : ℝ) (k : ℕ) : 0 < sk τ k := by
  unfold sk
  exact Real.rpow_pos_of_pos (by positivity) _

lemma S_base_le_one (k : ℕ) : 1 / ((k : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

lemma S_sk_le_one {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (k : ℕ) : sk τ k ≤ 1 := by
  unfold sk
  have := S_eta_pos h0 h1
  exact Real.rpow_le_one (by positivity) (S_base_le_one k) (by linarith)

lemma S_sk_sq (τ : ℝ) (k : ℕ) : sk τ k ^ 2 = (1 / ((k : ℝ) + 1)) ^ (2 / 3 + 2 * eta τ) := by
  unfold sk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

lemma S_sk_cube (τ : ℝ) (k : ℕ) : sk τ k ^ 3 = (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) := by
  unfold sk
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    gk τ k * sk τ k + sk τ k * Hk k * sk τ k + sigk k * |sk τ k| ^ 3 = 0 ∧
      0 ≤ sk τ k * Hk k * sk τ k + sigk k * |sk τ k| ^ 3 ∧
      0 < sigk k ∧ sigk (k + 1) ≤ sigk k ∧
      dataModel τ k (sk τ k) = fk τ k - 2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) ∧
      fk τ (k + 1) = dataModel τ k (sk τ k) ∧
      (∀ s : ℝ, dataModel τ k (sk τ k) ≤ dataModel τ k s) ∧
      sk τ k = xk τ (k + 1) - xk τ k ∧ 0 < sk τ k ∧ sk τ k ≤ 1 := by
  have hs0 := S_sk_pos τ k
  have hs1 := S_sk_le_one hτ0 hτ1 k
  have hsq := S_sk_sq τ k
  have hcube := S_sk_cube τ k
  have hg : gk τ k = -(sk τ k) ^ 2 := by
    unfold gk; rw [hsq]
  have habs : |sk τ k| = sk τ k := abs_of_pos hs0
  have hdm : dataModel τ k (sk τ k) = fk τ k - 2 / 3 * (sk τ k) ^ 3 := by
    unfold dataModel
    rw [hg, habs]
    simp [Hk, sigk]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hs0, hs1⟩
  · rw [hg, habs]; simp [Hk, sigk]; ring
  · rw [habs]; simp [Hk, sigk]; positivity
  · simp [sigk]
  · simp [sigk]
  · rw [hdm, hcube]
  · show fk τ k - 2 / 3 * (1 / ((k : ℝ) + 1)) ^ (1 + 3 * eta τ) = _
    rw [hdm, hcube]
  · intro s
    rw [hdm]
    unfold dataModel
    rw [hg]
    simp only [Hk, sigk]
    have h3 : 0 ≤ (|s| - sk τ k) ^ 2 * (|s| + 2 * sk τ k) :=
      mul_nonneg (sq_nonneg _) (by positivity)
    have h4 : -(sk τ k) ^ 2 * s ≥ -(sk τ k) ^ 2 * |s| := by
      nlinarith [le_abs_self s, sq_nonneg (sk τ k)]
    have habs3 : |s| ^ 3 = |s| * |s| ^ 2 := by ring
    nlinarith [sq_abs s]
  · simp [xk]

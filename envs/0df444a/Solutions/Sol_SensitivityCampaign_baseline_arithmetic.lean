-- Prove2me | solution 1 for SensitivityCampaign.baseline_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-15T18:20:01.926214+00:00
-- url     : https://prove2.me/submissions/4078c0bd-5a61-440b-ac4f-62bcc5cef342

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1000
set_option Elab.async false
open Real

private lemma log_two_lower : (0.69314718055 : ℝ) ≤ log 2 := by
  have h := sum_range_le_log_div (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_three_upper : log 3 ≤ (1.09861228867 : ℝ) := by
  have h := log_div_le_sum_range_add (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_eleven_eighths_upper : log (11 / 8 : ℝ) ≤ (0.31845373112 : ℝ) := by
  have h := log_div_le_sum_range_add (x := (3 / 19 : ℝ)) (by norm_num) (by norm_num) 8
  norm_num [Finset.sum_range_succ] at h
  linarith

private lemma log_twenty_two : log (22 : ℝ) = 4 * log 2 + log (11 / 8 : ℝ) := by
  have he : (22 : ℝ) = 2 ^ 4 * (11 / 8) := by norm_num
  rw [he, log_mul (by norm_num) (by norm_num), log_pow]
  norm_num

private lemma log_gap :
    (2.000252407 : ℝ) * (log 22 + 200 * log 3) ≤ 9 * log 2 + 400 * log 3 := by
  rw [log_twenty_two]
  nlinarith [log_two_lower, log_three_upper, log_eleven_eighths_upper]

theorem solution :
    let M : ℕ := 9 ^ 10
    ((2 * (9 + 2) * M ^ 10 : ℕ) : ℝ) ^ (2.000252407 : ℝ) ≤
      ((M ^ 2 * (2 * M ^ 2 + 1) ^ 9 : ℕ) : ℝ) := by
  dsimp only
  have hAeq : ((2 * (9 + 2) * (9 ^ 10) ^ 10 : ℕ) : ℝ) = 22 * (3 : ℝ) ^ 200 := by norm_num
  have hBeq : (((9 ^ 10) ^ 2 * (2 * (9 ^ 10) ^ 2 + 1) ^ 9 : ℕ) : ℝ) =
      (9 ^ 10 : ℝ) ^ 2 * (2 * (9 ^ 10 : ℝ) ^ 2 + 1) ^ 9 := by norm_num
  rw [hAeq, hBeq]
  have hlow : (2 : ℝ) ^ 9 * 3 ^ 400 ≤ (9 ^ 10) ^ 2 * (2 * (9 ^ 10) ^ 2 + 1) ^ 9 := by
    calc
      (2 : ℝ) ^ 9 * 3 ^ 400 = (9 ^ 10) ^ 2 * (2 * (9 ^ 10) ^ 2) ^ 9 := by ring
      _ ≤ _ := by gcongr; norm_num
  apply le_trans _ hlow
  apply (log_le_log_iff (rpow_pos_of_pos (by positivity) _) (by positivity)).mp
  rw [log_rpow (by positivity), log_mul (by norm_num) (by positivity), log_pow,
      log_mul (by positivity) (by positivity), log_pow, log_pow]
  convert log_gap using 1 <;> norm_num

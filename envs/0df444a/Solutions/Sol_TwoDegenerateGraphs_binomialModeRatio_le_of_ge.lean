-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialModeRatio_le_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:24:47.545633+00:00
-- url     : https://prove2.me/submissions/3d7a31b0-3a99-4465-8d1f-8523ab21beec

-- Adapted from openai/ten-proofs, commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6.
-- Source: CompactnessAndDegeneracy.lean; submitted to the exact Prove2Me statement.
import Definitions.Def_CompactnessAndDegeneracy
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Lean.Elab.Tactic.Omega
open TwoDegenerateGraphs
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith


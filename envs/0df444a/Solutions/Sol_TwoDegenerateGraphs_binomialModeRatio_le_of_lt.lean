-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialModeRatio_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:24:49.290441+00:00
-- url     : https://prove2.me/submissions/c9ac5d90-4223-4ae8-825b-a4dc5c07681e

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
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith


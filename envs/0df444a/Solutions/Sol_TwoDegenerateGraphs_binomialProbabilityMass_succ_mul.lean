-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialProbabilityMass_succ_mul
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:24:51.003769+00:00
-- url     : https://prove2.me/submissions/d1eb8975-035e-4d96-bc4f-8505895df1d6

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
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1) probability *
        ((successCount + 1 : ℕ) : ℝ) * (1 - probability) =
      binomialProbabilityMass trialCount successCount probability *
        ((trialCount - successCount : ℕ) : ℝ) * probability := by
  have hc :
      ((trialCount.choose (successCount + 1) : ℕ) : ℝ) *
          ((successCount + 1 : ℕ) : ℝ) =
        ((trialCount.choose successCount : ℕ) : ℝ) *
          ((trialCount - successCount : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq trialCount successCount
  have hs : trialCount - successCount =
      (trialCount - (successCount + 1)) + 1 := by omega
  unfold binomialProbabilityMass
  rw [hs] at hc ⊢
  simp only [pow_succ]
  linear_combination
    (probability ^ successCount *
      (1 - probability) ^ (trialCount - (successCount + 1)) *
      probability * (1 - probability)) * hc


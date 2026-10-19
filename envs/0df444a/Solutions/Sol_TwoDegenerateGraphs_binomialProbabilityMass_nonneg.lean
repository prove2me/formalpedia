-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialProbabilityMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:24:45.660888+00:00
-- url     : https://prove2.me/submissions/2e23f8ce-4110-4fc2-bcc3-b5ef362deaac

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
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity


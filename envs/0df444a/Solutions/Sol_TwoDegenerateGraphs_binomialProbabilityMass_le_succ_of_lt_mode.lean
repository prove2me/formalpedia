-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialProbabilityMass_le_succ_of_lt_mode
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-19T11:28:33.510522+00:00
-- url     : https://prove2.me/submissions/d7813114-5c16-4aed-98a0-edbf2335301f

-- Adapted from openai/ten-proofs, commit 94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6.
-- Source: CompactnessAndDegeneracy.lean. All supporting lemmas are proved in this file.
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

private theorem b3_binomialProbabilityMass_nonneg
    (trialCount successCount : ℕ) (probability : ℝ)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    0 ≤ binomialProbabilityMass trialCount successCount probability := by
  unfold binomialProbabilityMass
  have hcomplement : 0 ≤ 1 - probability := by linarith
  positivity


private theorem b3_binomialModeRatio_le_of_lt
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


private theorem b3_binomialProbabilityMass_succ_mul
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


theorem solution
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : successCount < mode) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := b3_binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := b3_binomialModeRatio_le_of_lt
    trialCount mode successCount hmode.le hcount
  have hidentity := b3_binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    (show successCount < trialCount by omega)
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hmass
    _ = binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]



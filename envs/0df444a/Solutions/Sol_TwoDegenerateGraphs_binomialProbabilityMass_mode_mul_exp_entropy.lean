-- Prove2me | solution 1 for TwoDegenerateGraphs.binomialProbabilityMass_mode_mul_exp_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/217580c8-0562-4390-b5d0-c21160bd1d20

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by
  by_cases hzero : mode = 0
  · subst mode
    simp [binomialProbabilityMass]
  by_cases hfull : mode = trialCount
  · subst mode
    have htrials : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    simp [binomialProbabilityMass, htrials]
  have hmode_pos : 0 < mode := Nat.pos_of_ne_zero hzero
  have hmode_lt : mode < trialCount :=
    lt_of_le_of_ne hmode hfull
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hprobability : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode_lt
  have hcomplement : 0 < 1 - probability := by
    linarith
  have hproduct :
      0 < probability ^ mode *
        (1 - probability) ^ (trialCount - mode) := by
    positivity
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(mode : ℝ) * Real.log probability -
          ((trialCount - mode : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hmode]
    dsimp [probability]
    field_simp [htrials_real.ne']
    ring
  have hlog :
      Real.log
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode)) +
        (trialCount : ℝ) * Real.binEntropy probability = 0 := by
    rw [Real.log_mul
      (pow_pos hprobability mode).ne'
      (pow_pos hcomplement (trialCount - mode)).ne',
      Real.log_pow, Real.log_pow, hentropy]
    ring
  change
    binomialProbabilityMass trialCount mode probability *
      Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ)
  calc
    binomialProbabilityMass trialCount mode probability *
        Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ) *
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode) *
          Real.exp ((trialCount : ℝ) * Real.binEntropy probability)) := by
        unfold binomialProbabilityMass
        ring
    _ = (trialCount.choose mode : ℝ) *
        Real.exp
          (Real.log
              (probability ^ mode *
                (1 - probability) ^ (trialCount - mode)) +
            (trialCount : ℝ) * Real.binEntropy probability) := by
          rw [Real.exp_add, Real.exp_log hproduct]
    _ = (trialCount.choose mode : ℝ) := by
      rw [hlog]
      simp
end TwoDegenerateGraphs

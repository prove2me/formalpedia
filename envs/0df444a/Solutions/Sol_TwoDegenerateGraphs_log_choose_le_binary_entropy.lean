-- Prove2me | solution 1 for TwoDegenerateGraphs.log_choose_le_binary_entropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/8c7463d2-40b6-4100-9990-286005ffe66b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binomial_probability_term_le_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.log (trialCount.choose successCount : ℝ) ≤
      (trialCount : ℝ) *
        Real.binEntropy ((successCount : ℝ) / (trialCount : ℝ)) := by
  by_cases hzero : successCount = 0
  · subst successCount
    simp
  by_cases hfull : successCount = trialCount
  · subst successCount
    by_cases htrials : trialCount = 0
    · simp [htrials]
    · have htrials_real : (trialCount : ℝ) ≠ 0 := by
        exact_mod_cast htrials
      simp [htrials_real]
  have hsuccess : 0 < successCount := Nat.pos_of_ne_zero hzero
  have hstrict : successCount < trialCount :=
    lt_of_le_of_ne hcount hfull
  have htrials : 0 < trialCount :=
    lt_of_lt_of_le hsuccess hcount
  let probability : ℝ :=
    (successCount : ℝ) / (trialCount : ℝ)
  have hprobability_pos : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_lt_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one (by exact_mod_cast htrials)).mpr
    exact_mod_cast hstrict
  have hcomplement : 0 < 1 - probability :=
    sub_pos.mpr hprobability_lt_one
  have hchoose : 0 < (trialCount.choose successCount : ℝ) := by
    exact_mod_cast Nat.choose_pos hcount
  have hmass := binomial_probability_term_le_one
    trialCount successCount probability hcount
    hprobability_pos.le hprobability_lt_one.le
  have hproduct :
      0 < (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) := by
    positivity
  have hlogmass := Real.log_le_log hproduct hmass
  simp only [Real.log_one] at hlogmass
  rw [Real.log_mul
      (mul_pos hchoose (pow_pos hprobability_pos _)).ne'
      (pow_pos hcomplement _).ne',
    Real.log_mul hchoose.ne' (pow_pos hprobability_pos _).ne',
    Real.log_pow, Real.log_pow] at hlogmass
  have htrials_real : (trialCount : ℝ) ≠ 0 := by
    exact_mod_cast htrials.ne'
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(successCount : ℝ) * Real.log probability -
          ((trialCount - successCount : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hcount]
    dsimp [probability]
    field_simp [htrials_real]
    ring
  change Real.log (trialCount.choose successCount : ℝ) ≤
    (trialCount : ℝ) * Real.binEntropy probability
  rw [hentropy]
  linarith
end TwoDegenerateGraphs

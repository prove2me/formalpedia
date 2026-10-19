-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialProbabilityMass_succ_le_of_ge_mode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/f8d37421-4ae4-4a45-aaf8-d5be7bf6eb19

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_nonneg
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_succ_mul
import Theorems.Thm_TwoDegenerateGraphs_binomialModeRatio_le_of_ge

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount successCount
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
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_ge
    trialCount mode successCount htrials hmode.le hcount hsuccess
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ)) hsuccess
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) =
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]
    _ ≤ binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hmass
end TwoDegenerateGraphs

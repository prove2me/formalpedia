-- Prove2me | solution 1 for TwoDegenerateGraphs.exp_binary_entropy_div_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/3e7adada-53b9-46bd-a064-3fc79f125483

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_mode_ge_inverse
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_mode_mul_exp_entropy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by
  have hmode := binomialProbabilityMass_mode_ge_inverse
    trialCount successCount hcount
  have hexponential :
      0 ≤ Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) =
      (1 / ((trialCount + 1 : ℕ) : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) := by
        ring
    _ ≤ binomialProbabilityMass trialCount successCount
          ((successCount : ℝ) / (trialCount : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) :=
      mul_le_mul_of_nonneg_right hmode hexponential
    _ = (trialCount.choose successCount : ℝ) :=
      binomialProbabilityMass_mode_mul_exp_entropy
        trialCount successCount hcount
end TwoDegenerateGraphs

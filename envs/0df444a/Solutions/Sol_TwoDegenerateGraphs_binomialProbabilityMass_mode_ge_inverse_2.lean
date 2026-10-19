-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialProbabilityMass_mode_ge_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/daa7c1e3-8bcd-4496-9a86-59626a5efd24

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_le_mode
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_sum_eq_one

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have hdenominator : 0 < ((trialCount + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenominator).mpr
  calc
    (1 : ℝ) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount successCount
          ((mode : ℝ) / (trialCount : ℝ)) :=
      (binomialProbabilityMass_sum_eq_one
        trialCount ((mode : ℝ) / (trialCount : ℝ))).symm
    _ ≤ ∑ _successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) := by
      apply Finset.sum_le_sum
      intro successCount hsuccess
      apply binomialProbabilityMass_le_mode
        trialCount mode successCount hmode
      have hbound := Finset.mem_range.mp hsuccess
      omega
    _ = binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) *
        ((trialCount + 1 : ℕ) : ℝ) := by
      simp [nsmul_eq_mul]
      ring
end TwoDegenerateGraphs

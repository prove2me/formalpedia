-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialProbabilityMass_sum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/b666e490-66ff-45d3-a127-7e6e50fb43b8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount : ℕ) (probability : ℝ) :
    (∑ successCount ∈ Finset.range (trialCount + 1),
      binomialProbabilityMass trialCount successCount probability) = 1 := by
  unfold binomialProbabilityMass
  calc
    (∑ successCount ∈ Finset.range (trialCount + 1),
      (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount)) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        probability ^ successCount *
          (1 - probability) ^ (trialCount - successCount) *
          (trialCount.choose successCount : ℝ) := by
            apply Finset.sum_congr rfl
            intro successCount _
            ring
    _ = (probability + (1 - probability)) ^ trialCount :=
      (add_pow probability (1 - probability) trialCount).symm
    _ = 1 := by
      rw [show probability + (1 - probability) = 1 by ring]
      simp
end TwoDegenerateGraphs

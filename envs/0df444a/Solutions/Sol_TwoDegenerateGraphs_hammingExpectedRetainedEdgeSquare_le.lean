-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedEdgeSquare_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/2d2d8c70-392a-48ed-99c2-9b80a95af860

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdgePair_sum_const
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdgePairSharedLeft_sum_const
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdgePairSharedRight_sum_const
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdgePairIdentical_sum_const
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeCount_eq
import Theorems.Thm_TwoDegenerateGraphs_hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  classical
  have hpoint
      (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
      (if hammingDist firstLeft firstRight ≤ radius ∧
          hammingDist secondLeft secondRight ≤ radius then
        hammingRetentionProbability dimension ^ 4 +
          (if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0) +
          (if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0)
      else 0) =
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          hammingRetentionProbability dimension ^ 4 else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstRight = secondRight then
            hammingRetentionProbability dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft ∧ firstRight = secondRight then
            hammingRetentionProbability dimension ^ 2 else 0
        else 0) := by
    split <;> simp
  calc
    hammingExpectedRetainedEdgeSquare dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                hammingRetentionProbability dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧ firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 :=
        hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
          dimension radius
    _ = hammingExpectedRetainedEdgeCount dimension radius ^ 2 +
        hammingExpectedRetainedEdgeCount dimension radius +
        2 * hammingRetentionProbability dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hammingWordEdgePair_sum_const,
        hammingWordEdgePairSharedLeft_sum_const,
        hammingWordEdgePairSharedRight_sum_const,
        hammingWordEdgePairIdentical_sum_const,
        hammingExpectedRetainedEdgeCount_eq]
      ring
end TwoDegenerateGraphs

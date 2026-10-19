-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingExpectedRetainedEdgeSquare_le_endpoint_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/58a76588-4744-412f-a49b-bc6183ce3d7d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_edgePair_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) :
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
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    hammingRetentionProbability dimension ^ 2 else 0)
              else 0 := by
  unfold hammingExpectedRetainedEdgeSquare
  apply Finset.sum_le_sum
  intro firstLeft _
  apply Finset.sum_le_sum
  intro firstRight _
  apply Finset.sum_le_sum
  intro secondLeft _
  apply Finset.sum_le_sum
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    exact hammingRetentionMeasure_real_contains_edgePair_le
      dimension firstLeft firstRight secondLeft secondRight
  · simp [hedge]
end TwoDegenerateGraphs

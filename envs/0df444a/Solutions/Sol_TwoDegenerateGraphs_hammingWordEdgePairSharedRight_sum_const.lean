-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingWordEdgePairSharedRight_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/17026dce-f8f4-4b33-b77a-2548b4de4b27

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdgePairSharedLeft_sum_const

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  calc
    (∑ firstLeft : HammingWord dimension,
      ∑ firstRight : HammingWord dimension,
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if firstRight = secondRight then weight else 0
            else 0) =
      (∑ firstRight : HammingWord dimension,
        ∑ firstLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            ∑ secondLeft : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if firstRight = secondRight then weight else 0
              else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro firstRight _
        apply Finset.sum_congr rfl
        intro firstLeft _
        rw [Finset.sum_comm]
    _ = ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
      simpa only [hammingDist_comm] using
        hammingWordEdgePairSharedLeft_sum_const dimension radius weight
end TwoDegenerateGraphs

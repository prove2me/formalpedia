-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingWordEdgePairIdentical_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/a37404e4-d96f-44c1-9f90-254bede130a3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingWordEdge_sum_const

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
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by
  classical
  calc
    _ = ∑ firstLeft : HammingWord dimension,
          ∑ firstRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius then weight else 0 := by
      apply Finset.sum_congr rfl
      intro firstLeft _
      apply Finset.sum_congr rfl
      intro firstRight _
      by_cases hedge : hammingDist firstLeft firstRight ≤ radius
      · simp only [hedge, true_and, if_true]
        have hpoint (secondLeft secondRight : HammingWord dimension) :
            (if hammingDist secondLeft secondRight ≤ radius then
              if firstLeft = secondLeft ∧ firstRight = secondRight then
                weight else 0
            else 0) =
              if firstLeft = secondLeft then
                if firstRight = secondRight then weight else 0
              else 0 := by
          split_ifs <;> simp_all
        simp_rw [hpoint]
        simp
      · simp [hedge]
    _ = _ := hammingWordEdge_sum_const dimension radius weight
end TwoDegenerateGraphs

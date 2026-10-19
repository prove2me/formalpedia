-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingWordEdgePair_sum_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/fb35709b-3844-4448-8cec-2a5739b867be

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
              weight
            else 0) =
      ((2 ^ dimension : ℕ) : ℝ) ^ 2 *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ^ 2 * weight := by
  classical
  have hinner (firstLeft firstRight : HammingWord dimension) :
      (∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            weight
          else 0) =
        if hammingDist firstLeft firstRight ≤ radius then
          ((2 ^ dimension : ℕ) : ℝ) *
            ((∑ distance ∈ Finset.range (radius + 1),
              dimension.choose distance : ℕ) : ℝ) * weight
        else 0 := by
    by_cases hedge : hammingDist firstLeft firstRight ≤ radius
    · simp only [hedge, true_and, if_true]
      exact hammingWordEdge_sum_const dimension radius weight
    · simp [hedge]
  simp_rw [hinner]
  rw [hammingWordEdge_sum_const]
  ring
end TwoDegenerateGraphs

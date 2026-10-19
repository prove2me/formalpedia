-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/ab9e2a19-9715-4781-b509-07faf5617083

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
open Classical
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained ^ 2 =
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0 := by
  classical
  unfold hammingRetainedEdgeCount
  rw [pow_two, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro firstRight _
  apply Finset.sum_congr rfl
  intro secondLeft _
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hfirst_edge : hammingDist firstLeft firstRight ≤ radius <;>
    by_cases hsecond_edge : hammingDist secondLeft secondRight ≤ radius <;>
    by_cases hfirst_left : (false, firstLeft) ∈ retained <;>
    by_cases hfirst_right : (true, firstRight) ∈ retained <;>
    by_cases hsecond_left : (false, secondLeft) ∈ retained <;>
    by_cases hsecond_right : (true, secondRight) ∈ retained <;>
    simp [hfirst_edge, hsecond_edge, hfirst_left, hfirst_right,
      hsecond_left, hsecond_right]
end TwoDegenerateGraphs

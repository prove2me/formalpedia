-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_eq_wordEdges_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/ff75a55b-bad9-41f4-87a9-a2020eda9b85

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension radius : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
  classical
  unfold hammingRetainedEdgeCount
  calc
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0) =
      ∑ edge : HammingWord dimension × HammingWord dimension,
        if hammingDist edge.1 edge.2 ≤ radius ∧
            (false, edge.1) ∈ retained ∧ (true, edge.2) ∈ retained
        then (1 : ℝ) else 0 := by
          rw [Fintype.sum_prod_type]
    _ = ∑ _edge ∈ retainedHammingWordEdges dimension radius retained,
          (1 : ℝ) := by
      unfold retainedHammingWordEdges
      rw [← Finset.sum_filter]
    _ = ((retainedHammingWordEdges dimension radius retained).card : ℝ) := by
      simp
end TwoDegenerateGraphs

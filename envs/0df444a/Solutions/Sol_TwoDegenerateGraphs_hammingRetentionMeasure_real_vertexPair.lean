-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_vertexPair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/796e1573-bfa5-4a59-bae6-fd30d77f8da7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_pair
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_vertex

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        hammingRetentionProbability dimension
      else hammingRetentionProbability dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, hammingRetentionMeasure_real_contains_vertex]
    simp
  · rw [hammingRetentionMeasure_real_contains_pair
      dimension first second hequal]
    simp [hequal]
end TwoDegenerateGraphs

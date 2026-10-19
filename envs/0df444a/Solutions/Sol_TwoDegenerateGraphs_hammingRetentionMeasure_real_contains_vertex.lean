-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_contains_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:07.571959+00:00
-- url     : https://prove2.me/submissions/8d0a35e8-3790-44e1-9354-68ac0c4056c1

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_finset

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      hammingRetentionProbability dimension := by
  classical
  simpa using
    hammingRetentionMeasure_real_contains_finset dimension {vertex}
end TwoDegenerateGraphs

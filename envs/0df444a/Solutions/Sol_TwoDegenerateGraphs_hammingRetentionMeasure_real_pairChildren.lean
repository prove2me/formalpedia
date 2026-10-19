-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetentionMeasure_real_pairChildren
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/9a451208-63e8-4418-b36c-9c2aaa0fa4a0

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_contains_finset
import Theorems.Thm_TwoDegenerateGraphs_pairChildVertexFinset_card

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by
  classical
  have hevent :
      pairChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ pairChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [pairChildRetentionEvent, pairChildVertexFinset]
  rw [hevent, hammingRetentionMeasure_real_contains_finset,
    pairChildVertexFinset_card side children hinjective]
end TwoDegenerateGraphs

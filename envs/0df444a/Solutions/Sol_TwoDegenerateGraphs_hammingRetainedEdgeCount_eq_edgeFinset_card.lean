-- Prove2me | solution 1 for TwoDegenerateGraphs.hammingRetainedEdgeCount_eq_edgeFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/b30616d6-e5a3-4271-a502-0013e5b330bf

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_hammingRetainedEdgeCount_eq_wordEdges_card
import Theorems.Thm_TwoDegenerateGraphs_retainedHammingHost_edgeFinset_card

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
    hammingRetainedEdgeCount dimension radius retained =
      ((retainedHammingHost dimension radius retained).edgeFinset.card : ℝ) := by
  rw [hammingRetainedEdgeCount_eq_wordEdges_card,
    retainedHammingHost_edgeFinset_card]
end TwoDegenerateGraphs

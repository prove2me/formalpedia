-- Prove2me | solution 1 for TwoDegenerateGraphs.pairChildVertexFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/71477b0b-3af8-44e3-9e33-202f2bae205d

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

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
    (pairChildVertexFinset side children).card = parentCount.choose 2 := by
  classical
  unfold pairChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, pairLayer_card_succ parentCount 0,
      pairLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)
end TwoDegenerateGraphs

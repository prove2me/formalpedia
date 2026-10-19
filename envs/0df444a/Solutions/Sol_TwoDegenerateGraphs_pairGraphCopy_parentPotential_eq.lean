-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_parentPotential_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/028dc013-1da2-4e41-abf5-6ce383f262be

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_booleanWordOnes_card_equiv

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairParentArrayEntropyPotential
        (pairGraphCopyParentWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val, by omega⟩ := by
  unfold pairParentArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount pairGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (pairLayerFinEquiv baseSize layer.val).symm
    (fun vertex : PairLayer baseSize layer.val =>
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          vertex)).val.2 coordinate)]
end TwoDegenerateGraphs

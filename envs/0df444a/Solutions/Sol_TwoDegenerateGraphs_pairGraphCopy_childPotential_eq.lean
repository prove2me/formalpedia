-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_childPotential_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/f5d369bc-6677-4255-bd40-0639272f84b1

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
    pairChildArrayEntropyPotential
        (pairGraphCopyChildWords retained copy layer) =
      pairGraphCopyLayerPotential retained copy
        ⟨layer.val + 1, by omega⟩ := by
  unfold pairChildArrayEntropyPotential
    pairGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairChildCoordinateOneCount pairGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (pairLayerPairEquiv baseSize layer.val)
    (fun vertex : PairLayer baseSize (layer.val + 1) =>
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          vertex)).val.2 coordinate)]
  rw [pairLayer_card_succ]
end TwoDegenerateGraphs

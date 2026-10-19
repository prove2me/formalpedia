-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopyChildWords_retained
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/fa8eb91b-d51e-4765-8220-206d30714d14

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_child_layer_side_eq

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
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1) :
    retained ∈
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference)
        (pairGraphCopyChildWords retained copy layer) := by
  intro pair
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) reference)
    ((pairLayerPairEquiv baseSize layer.val) pair)
  have hretained :=
    (copy
      (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((pairLayerPairEquiv baseSize layer.val) pair))).property
  change
    (pairGraphCopyChildSide retained copy layer reference,
      pairGraphCopyChildWords retained copy layer pair) ∈ retained
  unfold pairGraphCopyChildSide pairGraphCopyChildWords
  rw [hside]
  exact hretained
end TwoDegenerateGraphs

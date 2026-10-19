-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_parent_child_hammingDist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/50166e20-eaab-4ec0-abbc-59de426bd751

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_parent_child_adj
import Theorems.Thm_TwoDegenerateGraphs_hammingHost_adj_iff

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
    (pair :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (parent :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 0)
    (hparent : parent ∈ pair.val) :
    hammingDist
      (pairGraphCopyParentWords retained copy layer parent)
      (pairGraphCopyChildWords retained copy layer pair) ≤ radius := by
  have hactualParent :
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        ((pairLayerPairEquiv baseSize layer.val) pair).val := by
    change
      (pairLayerFinEquiv baseSize layer.val).symm parent ∈
        pair.val.map
          (pairLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := pairGraph_parent_child_adj
    baseSize depth layer.val (by omega)
      ((pairLayerPairEquiv baseSize layer.val) pair)
      ((pairLayerFinEquiv baseSize layer.val).symm parent)
      hactualParent
  have hedge := copy.toHom.map_rel hsource
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) pair))).val
      (copy
        (pairLayerEmbedding baseSize depth layer.val (by omega)
          ((pairLayerFinEquiv baseSize layer.val).symm parent))).val at hedge
  have hdist :=
    ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [pairGraphCopyParentWords, pairGraphCopyChildWords,
    hammingDist_comm] using hdist
end TwoDegenerateGraphs

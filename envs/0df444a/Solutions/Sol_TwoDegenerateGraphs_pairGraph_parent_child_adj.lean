-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraph_parent_child_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:06.124263+00:00
-- url     : https://prove2.me/submissions/7436e272-bf98-4102-81f3-b5f6e63ffcdd

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_ParentSystem_graph_adj_iff

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (ParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val)
      hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        pairParents baseSize depth
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer child)
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        child.val.map
          (pairLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
end TwoDegenerateGraphs

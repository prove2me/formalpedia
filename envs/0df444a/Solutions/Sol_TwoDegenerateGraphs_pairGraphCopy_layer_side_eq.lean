-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_layer_side_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/807c51f2-b665-4bcd-8019-a886f5f585fc

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
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize layer) :
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second
    rfl
  · let bridge : PairLayer baseSize (layer + 1) :=
      ⟨{first, second}, Finset.card_pair hequal⟩
    have hfirst_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) first) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge first
        (by simp [bridge])
    have hsecond_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) second) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge second
        (by simp [bridge])
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val at hfirst_edge
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val at hsecond_edge
    have hfirst_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer bridge)).val.1 <;>
      cases hfirst :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val.1 <;>
      cases hsecond :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val.1 <;>
      simp_all
end TwoDegenerateGraphs

-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_child_layer_side_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/f4632dfb-9611-436f-a822-e3eacd5b3f10

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_parent_child_adj
import Theorems.Thm_TwoDegenerateGraphs_hammingHost_adj_iff
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_layer_side_eq

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
    (first second : PairLayer baseSize (layer + 1)) :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [first.property]
    norm_num
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [second.property]
    norm_num
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := pairGraphCopy_layer_side_eq
    retained copy layer hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer first firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer second secondParent hsecondParent)
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer first)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val at hfirst_edge
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val at hsecond_edge
  have hfirst_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hfirst :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 <;>
    cases hsecond :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val.1 <;>
    cases hfirstParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val.1 <;>
    cases hsecondParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val.1 <;>
    simp_all
end TwoDegenerateGraphs

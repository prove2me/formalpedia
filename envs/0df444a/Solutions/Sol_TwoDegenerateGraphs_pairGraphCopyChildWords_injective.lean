-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopyChildWords_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/ddd3017c-5d28-452e-9e98-e001f9fb7fda

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
    (layer : Fin depth) :
    Function.Injective (pairGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := pairGraphCopy_child_layer_side_eq
    retained copy layer.val (by omega)
    ((pairLayerPairEquiv baseSize layer.val) first)
    ((pairLayerPairEquiv baseSize layer.val) second)
  have hvertices :
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first))).val =
      (copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second))).val := by
    apply Prod.ext
    · exact hside
    · exact hwords
  have himages :
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) first)) =
      copy
        (pairLayerEmbedding baseSize depth (layer.val + 1) (by omega)
          ((pairLayerPairEquiv baseSize layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have hpairs :=
    (pairLayerEmbedding baseSize depth (layer.val + 1)
      (by omega)).injective hsources
  exact (pairLayerPairEquiv baseSize layer.val).injective hpairs
end TwoDegenerateGraphs

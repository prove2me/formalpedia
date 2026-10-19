-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion_and_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/f7b41d3d-b796-49f8-8bb2-82910e8d8a80

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraph_free_of_layer_exclusion_and_disagreement

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    {baseSize depth dimension radius : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack)
    (hdisagreement :
      ∀ (copy : SimpleGraph.Copy
          (pairParentSystem baseSize depth).graph
          (retainedHammingHost dimension radius retained))
        (layer : Fin depth),
          pairChildArrayAverageDisagreement
            (hbase.trans
              (pairLayer_card_ge_base baseSize layer.val hbase))
            (pairGraphCopyParentWords retained copy layer)
            (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension radius retained) := by
  exact (SimpleGraph.free_congr_left
    (pairGraphOverFinIso baseSize depth)).mp
      (pairGraph_free_of_layer_exclusion_and_disagreement
        hbase hdimension hdepth retained hexclusion herror hdisagreement)
end TwoDegenerateGraphs

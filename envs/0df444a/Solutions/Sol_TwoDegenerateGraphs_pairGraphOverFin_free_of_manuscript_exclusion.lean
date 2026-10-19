-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_free_of_manuscript_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/6605968c-d69d-4b64-b08a-2a55469b6a60

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_free_of_layer_exclusion
import Theorems.Thm_TwoDegenerateGraphs_manuscriptHammingRadius_le

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable
namespace TwoDegenerateGraphs
theorem _root_.solution
    {baseSize depth dimension : ℕ}
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
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained) := by
  exact pairGraphOverFin_free_of_layer_exclusion
    hbase hdimension hdepth
    (manuscriptHammingRadius_le dimension)
    retained hexclusion herror
end TwoDegenerateGraphs

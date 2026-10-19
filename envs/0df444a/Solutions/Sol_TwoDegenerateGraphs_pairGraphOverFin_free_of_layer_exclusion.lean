-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/12c36398-725c-47e2-a6a5-dbc8c8e32e9f

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_averageDisagreement_le_tau
import Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_free_of_layer_exclusion_and_disagreement

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
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
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
      (retainedHammingHost dimension radius retained) := by
  apply pairGraphOverFin_free_of_layer_exclusion_and_disagreement
    hbase hdimension hdepth retained hexclusion herror
  intro copy layer
  exact pairGraphCopy_averageDisagreement_le_tau
    hbase hdimension hradius retained copy layer
end TwoDegenerateGraphs

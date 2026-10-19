-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_averageDisagreement_le_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/4dcb9218-b321-4b2d-884d-b7a23b30c70b

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairChildArrayAverageDisagreement_le_radius
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_parent_child_hammingDist_le

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
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) := by
  apply pairChildArrayAverageDisagreement_le_radius
    (hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase))
    hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
    radius
  intro pair parent hparent
  exact pairGraphCopy_parent_child_hammingDist_le
    retained copy layer pair parent hparent
end TwoDegenerateGraphs

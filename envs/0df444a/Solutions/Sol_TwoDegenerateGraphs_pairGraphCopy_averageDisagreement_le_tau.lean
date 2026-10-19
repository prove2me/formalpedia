-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_averageDisagreement_le_tau
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/ea9d8cb0-b49a-457c-91c8-7af7253a2c47

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_averageDisagreement_le_radius

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
    (hradius : (radius : ℝ) ≤ tau * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤ tau := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    pairChildArrayAverageDisagreement
      (hbase.trans
        (pairLayer_card_ge_base baseSize layer.val hbase))
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        (radius : ℝ) / (dimension : ℝ) :=
      pairGraphCopy_averageDisagreement_le_radius
        hbase hdimension retained copy layer
    _ ≤ tau :=
      (div_le_iff₀ hdimension_real).mpr hradius
end TwoDegenerateGraphs

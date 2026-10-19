-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_layer_entropy_upper_of_disagreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:08.630233+00:00
-- url     : https://prove2.me/submissions/2578b54a-14d0-4a10-9f2f-4bf6a8da0ac5

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairChildArrayEntropy_empirical_bound
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_parentPotential_eq
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopy_childPotential_eq

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
    (layer : Fin depth)
    (hdisagreement :
      pairChildArrayAverageDisagreement
        (hbase.trans
          (pairLayer_card_ge_base baseSize layer.val hbase))
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ tau) :
    pairChildArrayEntropy
      (pairGraphCopyParentWords retained copy layer)
      (pairGraphCopyChildWords retained copy layer) ≤
        entropyLowerEndpoint +
          (pairGraphCopyLayerPotential retained copy
              ⟨layer.val + 1, by omega⟩ -
            pairGraphCopyLayerPotential retained copy
              ⟨layer.val, by omega⟩) / 2 +
          empiricalEntropyError
            (Fintype.card (PairLayer baseSize layer.val)) := by
  have hparents :
      4 ≤ Fintype.card (PairLayer baseSize layer.val) :=
    hbase.trans
      (pairLayer_card_ge_base baseSize layer.val hbase)
  have hbound := pairChildArrayEntropy_empirical_bound
    hparents hdimension
    (pairGraphCopyParentWords retained copy layer)
    (pairGraphCopyChildWords retained copy layer)
  rw [pairGraphCopy_childPotential_eq retained copy layer,
    pairGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hscaled := mul_le_mul_of_nonneg_left
    hdisagreement logTwo_three_pos.le
  unfold entropyLowerEndpoint
  nlinarith
end TwoDegenerateGraphs

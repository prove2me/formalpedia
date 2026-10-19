-- Prove2me | solution 1 for TwoDegenerateGraphs.pairGraphCopy_entropy_lower_of_exclusion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/c73457cf-86d3-4080-9a7e-253886277137

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopyChildWords_injective
import Theorems.Thm_TwoDegenerateGraphs_pairGraphCopyChildWords_retained

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
    (layer : Fin depth)
    (reference :
      PairLayer (Fintype.card (PairLayer baseSize layer.val)) 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        badPairLayerRetentionEvent
          (Fintype.card (PairLayer baseSize layer.val)) dimension
          (pairGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      pairChildArrayEntropy
        (pairGraphCopyParentWords retained copy layer)
        (pairGraphCopyChildWords retained copy layer) ≤ threshold :=
    le_of_not_gt hnot
  have hbad_array :
      pairGraphCopyChildWords retained copy layer ∈
        badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold := by
    unfold badPairChildArrays
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      pairGraphCopyChildWords retained copy layer ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array,
        pairGraphCopyChildWords_injective retained copy layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (PairLayer baseSize layer.val)) →
          HammingWord dimension,
      badPairChildRetentionEvent parents
        (pairGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨pairGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badPairChildArrays
          (pairGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      pairChildRetentionEvent
        (pairGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨pairGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          pairGraphCopyChildWords_retained
            retained copy layer reference⟩⟩
end TwoDegenerateGraphs

-- Prove2me | solution 1 for QEC.Locality.minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:57.037403+00:00
-- url     : https://prove2.me/submissions/2122c5a2-6d7d-4e18-9720-02c92be00816

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_NoEdgeBetween_mono_spanningSubgraph
import Theorems.Thm_QEC_Locality_IsTwoThirdsBalancedVertexSeparator_mono_spanningSubgraph
import Theorems.Thm_QEC_Locality_exists_minimumTwoThirdsBalancedVertexSeparator
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_card


set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    (vertices : Finset ι) :
    minimumTwoThirdsBalancedVertexSeparatorSize H vertices ≤
      minimumTwoThirdsBalancedVertexSeparatorSize G vertices := by
  rcases exists_minimumTwoThirdsBalancedVertexSeparator G vertices with
    ⟨separator, hsubset, hbalanced, hcard⟩
  rw [← hcard]
  exact minimumTwoThirdsBalancedVertexSeparatorSize_le_card H vertices separator
    hsubset (hbalanced.mono_spanningSubgraph hHG)
end QEC.Locality

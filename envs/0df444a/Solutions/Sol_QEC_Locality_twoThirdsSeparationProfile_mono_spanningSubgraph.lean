-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_mono_spanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:26:41.927195+00:00
-- url     : https://prove2.me/submissions/38e61c2f-6dc1-411f-80e5-30cec1131f00

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile


set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G) (scale : Nat) :
    twoThirdsSeparationProfile H scale ≤ twoThirdsSeparationProfile G scale := by
  classical
  apply Finset.max'_le
  intro size hsize
  rcases Finset.mem_image.1 hsize with ⟨vertices, hvertices, rfl⟩
  rcases (mem_inducedVertexSetsAtMost_iff scale vertices).1 hvertices with
    ⟨hsubset, hcard⟩
  exact (minimumTwoThirdsBalancedVertexSeparatorSize_mono_spanningSubgraph
    hHG vertices).trans
      (minimumTwoThirdsBalancedVertexSeparatorSize_le_twoThirdsSeparationProfile
        G scale vertices hsubset hcard)
end QEC.Locality

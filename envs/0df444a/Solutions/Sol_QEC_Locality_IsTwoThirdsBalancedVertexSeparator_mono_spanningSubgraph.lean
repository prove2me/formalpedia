-- Prove2me | solution 1 for QEC.Locality.IsTwoThirdsBalancedVertexSeparator.mono_spanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:21:20.92988+00:00
-- url     : https://prove2.me/submissions/3678e8eb-bba7-4970-82ea-77dcc0061ceb

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision
import Theorems.Thm_QEC_Locality_NoEdgeBetween_mono_spanningSubgraph

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace IsTwoThirdsBalancedVertexSeparator
theorem _root_.solution
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {vertices separator : Finset ι}
    (hseparator : IsTwoThirdsBalancedVertexSeparator G vertices separator) :
    IsTwoThirdsBalancedVertexSeparator H vertices separator := by
  rcases hseparator with
    ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright, hnoEdge⟩
  exact ⟨left, right, hseparator, hpartition, hdisjoint, hleft, hright,
    hnoEdge.mono_spanningSubgraph hHG⟩
end IsTwoThirdsBalancedVertexSeparator
end QEC.Locality

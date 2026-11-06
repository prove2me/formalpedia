-- Prove2me | solution 1 for QEC.Locality.NoEdgeBetween.mono_spanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:34:13.064198+00:00
-- url     : https://prove2.me/submissions/3bf6faf4-97ec-4841-8e8a-fdbac4f187ac

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_CorrectablePartition_EdgeDivision

set_option autoImplicit false
open QEC QEC.Locality
open QEC Semantics Coding
universe u v w
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
namespace NoEdgeBetween
theorem _root_.solution
    {H G : ConnectivityGraph ι} (hHG : IsSpanningSubgraph H G)
    {left right : Finset ι} (hnoEdge : NoEdgeBetween G left right) :
    NoEdgeBetween H left right := by
  intro x hx y hy hHxy
  exact hnoEdge hx hy (hHG hHxy)
end NoEdgeBetween
end QEC.Locality

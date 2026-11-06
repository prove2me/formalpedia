-- Prove2me | solution 1 for QEC.Locality.edgeRestrictedGraph_isSpanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:28:49.219361+00:00
-- url     : https://prove2.me/submissions/18b00a43-c387-48e3-b476-9b0e85c740f3

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) :
    IsSpanningSubgraph (edgeRestrictedGraph G edges) G := by
  intro x y hxy
  exact hxy.1
end QEC.Locality

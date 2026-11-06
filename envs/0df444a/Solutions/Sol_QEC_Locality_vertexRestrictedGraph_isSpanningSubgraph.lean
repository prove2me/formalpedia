-- Prove2me | solution 1 for QEC.Locality.vertexRestrictedGraph_isSpanningSubgraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:28:18.697589+00:00
-- url     : https://prove2.me/submissions/68eee1c2-0357-4a66-8598-89beca1da505

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion

set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) :
    IsSpanningSubgraph (vertexRestrictedGraph G vertices) G := by
  intro x y hxy
  exact hxy.2.2
end QEC.Locality

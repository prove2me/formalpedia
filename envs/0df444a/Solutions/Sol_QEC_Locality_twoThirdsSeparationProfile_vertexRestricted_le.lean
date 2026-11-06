-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_vertexRestricted_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:14:35.228202+00:00
-- url     : https://prove2.me/submissions/91112bc7-47f7-4ee8-bac5-7e61ff30b476

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Theorems.Thm_QEC_Locality_vertexRestrictedGraph_isSpanningSubgraph
import Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_mono_spanningSubgraph


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (vertices : Finset ι) (scale : Nat) :
    twoThirdsSeparationProfile (vertexRestrictedGraph G vertices) scale ≤
      twoThirdsSeparationProfile G scale :=
  twoThirdsSeparationProfile_mono_spanningSubgraph
    (vertexRestrictedGraph_isSpanningSubgraph G vertices) scale
end QEC.Locality

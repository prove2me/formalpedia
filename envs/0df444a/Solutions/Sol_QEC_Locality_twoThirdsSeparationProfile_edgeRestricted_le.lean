-- Prove2me | solution 1 for QEC.Locality.twoThirdsSeparationProfile_edgeRestricted_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:32:10.668714+00:00
-- url     : https://prove2.me/submissions/af53660b-8397-4802-86e8-e506cb1278f4

import Definitions.Def_QEC_Locality_SeparatorProfile_EdgeDivision
import Definitions.Def_QEC_Locality_SeparatorProfile_Recursion
import Theorems.Thm_QEC_Locality_edgeRestrictedGraph_isSpanningSubgraph
import Theorems.Thm_QEC_Locality_twoThirdsSeparationProfile_mono_spanningSubgraph


set_option autoImplicit false
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (G : ConnectivityGraph ι) (edges : Finset (ι × ι)) (scale : Nat) :
    twoThirdsSeparationProfile (edgeRestrictedGraph G edges) scale ≤
      twoThirdsSeparationProfile G scale :=
  twoThirdsSeparationProfile_mono_spanningSubgraph
    (edgeRestrictedGraph_isSpanningSubgraph G edges) scale
end QEC.Locality

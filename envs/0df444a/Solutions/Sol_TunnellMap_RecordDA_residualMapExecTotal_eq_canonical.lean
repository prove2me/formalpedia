-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExecTotal_eq_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:57:15.938266+00:00
-- url     : https://prove2.me/submissions/aa0698a7-f963-4e1a-82b5-7c34b6df1482

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    residualMapExecTotal hn hnpos hsq hcard x =
      canonicalResidualMapOf hnpos (residualOrbitMatching hnpos hcard) x := by
  apply Option.some.inj
  exact (Option.some_get (by
      rw [residualMapExecOpt_eq_some hn hnpos hsq hcard x]
      rfl)).trans
    (residualMapExecOpt_eq_some hn hnpos hsq hcard x)
end TunnellMap.RecordDA

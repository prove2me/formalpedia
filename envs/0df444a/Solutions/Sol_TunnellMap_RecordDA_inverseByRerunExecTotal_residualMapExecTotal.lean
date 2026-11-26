-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExecTotal_residualMapExecTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:14:22.707929+00:00
-- url     : https://prove2.me/submissions/84cf3d57-3460-4067-9a10-d88f84f0f29c

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_RecordDA_residualMapExecTotal_eq_canonical
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExecTotal_residualMapExecOpt

set_option autoImplicit true
open TunnellMap
variable {n : ℤ}
open TunnellMap.RecordDA
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution
    (hn : Odd n) (hnpos : 0 < n) (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (x : BResidual n) :
    inverseByRerunExecTotal hn hnpos hsq hcard
      (residualMapExecTotal hn hnpos hsq hcard x) = x := by
  rw [residualMapExecTotal_eq_canonical,
    inverseByRerunExecTotal_residualMapExecOpt]
end TunnellMap.RecordDA

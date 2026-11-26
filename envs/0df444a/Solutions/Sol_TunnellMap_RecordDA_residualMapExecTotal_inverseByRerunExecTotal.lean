-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExecTotal_inverseByRerunExecTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:14:13.924214+00:00
-- url     : https://prove2.me/submissions/0c9b2809-eb5a-4fc4-97b4-eaae9841f420

import Definitions.Def_TunnellMap_ComputableFullMap
import Definitions.Def_TunnellMap_FallbackFreeMap
import Theorems.Thm_TunnellMap_RecordDA_residualMapExecTotal_eq_canonical
import Theorems.Thm_TunnellMap_RecordDA_residualMapExecOpt_inverseByRerunExecTotal

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
    (y : AResidual n) :
    residualMapExecTotal hn hnpos hsq hcard
      (inverseByRerunExecTotal hn hnpos hsq hcard y) = y := by
  rw [residualMapExecTotal_eq_canonical,
    residualMapExecOpt_inverseByRerunExecTotal]
end TunnellMap.RecordDA

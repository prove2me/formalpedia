-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExec_residualMapExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:02:02.459039+00:00
-- url     : https://prove2.me/submissions/bfd1b9a4-2d7b-4feb-9093-a7ddc1f6a913

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_canonicalResidualMap


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)]
variable [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (fallbackA : AResidual n) (fallbackB : BResidual n) (x : BResidual n) :
    inverseByRerunExec hsq fallbackB (residualMapExec hnpos hsq fallbackA x) = x := by
  rw [residualMapExec_eq hn hnpos hsq hcard, inverseByRerunExec_eq]
  exact inverseByRerun_canonicalResidualMap hn hnpos (framesExec hsq) hcard
    fallbackB x
end TunnellMap.RecordDA

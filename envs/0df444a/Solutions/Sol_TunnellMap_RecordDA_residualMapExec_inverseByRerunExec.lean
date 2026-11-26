-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExec_inverseByRerunExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:02:03.180666+00:00
-- url     : https://prove2.me/submissions/53291a31-2c86-4d28-8ef3-5ff461fbfa6e

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_canonicalResidualMap_inverseByRerun


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
    (fallbackA : AResidual n) (fallbackB : BResidual n) (y : AResidual n) :
    residualMapExec hnpos hsq fallbackA (inverseByRerunExec hsq fallbackB y) = y := by
  rw [residualMapExec_eq hn hnpos hsq hcard, inverseByRerunExec_eq]
  exact canonicalResidualMap_inverseByRerun hn hnpos (framesExec hsq) hcard
    fallbackB y
end TunnellMap.RecordDA

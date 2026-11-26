-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExec_eq_residualEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:02:34.494643+00:00
-- url     : https://prove2.me/submissions/5b3d0b87-f98a-4d4c-86a8-0f4b9dc57555

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_eq
import Theorems.Thm_TunnellMap_canonicalResidualMapOf_eq_residualEquivOfOrbitCard


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
    (fallback : AResidual n) (x : BResidual n) :
    residualMapExec hnpos hsq fallback x =
      residualEquivOfOrbitCard hnpos hcard x := by
  rw [residualMapExec_eq hn hnpos hsq hcard,
    canonicalResidualMapOf_eq_residualEquivOfOrbitCard hnpos hcard]
end TunnellMap.RecordDA

-- Prove2me | solution 1 for TunnellMap.RecordDA.runMatching_framesExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:31:54.444958+00:00
-- url     : https://prove2.me/submissions/25f31efe-1563-482d-a1dd-4f09eb677622

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_runMatching_eq


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (hsq : Squarefree n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    runMatching hn hnpos (framesExec hsq) hcard =
      residualOrbitMatching hnpos hcard :=
  runMatching_eq hn hnpos (framesExec hsq) hcard
end TunnellMap.RecordDA

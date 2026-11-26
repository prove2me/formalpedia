-- Prove2me | solution 1 for TunnellMap.RecordDA.residualMapExec_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:32:34.796878+00:00
-- url     : https://prove2.me/submissions/566b28b3-0f7c-4c88-bb4f-dac32600c084

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerunExec_residualMapExec
import Theorems.Thm_TunnellMap_RecordDA_residualMapExec_inverseByRerunExec

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
    (fallbackA : AResidual n) (fallbackB : BResidual n) :
    Function.Bijective (residualMapExec hnpos hsq fallbackA) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨inverseByRerunExec hsq fallbackB,
      inverseByRerunExec_residualMapExec hn hnpos hsq hcard fallbackA fallbackB,
      residualMapExec_inverseByRerunExec hn hnpos hsq hcard fallbackA fallbackB⟩
end TunnellMap.RecordDA

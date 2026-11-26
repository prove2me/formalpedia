-- Prove2me | solution 1 for TunnellMap.RecordDA.inverseByRerunExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:51:47.524002+00:00
-- url     : https://prove2.me/submissions/fa4187f0-1208-4ad4-95cd-c7f8fa0c8e5b

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_terminalRunExec_eq
import Theorems.Thm_TunnellMap_RecordDA_inverseByRerun_rerun


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable [Fintype (BOddRep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hsq : Squarefree n) (fallback : BResidual n)
    (y : AResidual n) :
    inverseByRerunExec hsq fallback y =
      inverseByRerun (framesExec hsq) fallback y := by
  rw [inverseByRerunExec, inverseByRerun_rerun, terminalRunExec_eq]
end TunnellMap.RecordDA

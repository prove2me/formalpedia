-- Prove2me | solution 1 for TunnellMap.RecordDA.framesExec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:08:58.765308+00:00
-- url     : https://prove2.me/submissions/a32796ef-4c41-4b5c-a5fb-d3d480dd97e2

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (hsq : Squarefree n) (s : BResidual n) :
    framesExec hsq s = frameExec hsq s := rfl
end TunnellMap.RecordDA

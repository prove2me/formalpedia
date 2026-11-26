-- Prove2me | solution 1 for TunnellMap.RecordDA.framesExec_deterministic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:30:26.354627+00:00
-- url     : https://prove2.me/submissions/48d3f0ce-699e-4984-92fd-a17c9431b98c

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
theorem _root_.solution (hsq hsq' : Squarefree n) :
    framesExec hsq = framesExec hsq' := rfl
end TunnellMap.RecordDA

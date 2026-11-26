-- Prove2me | solution 1 for TunnellMap.RecordDA.framesExecK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:21:54.604575+00:00
-- url     : https://prove2.me/submissions/da019bee-15c4-4d2e-9c92-52138170f333

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
import Theorems.Thm_TunnellMap_RecordDA_frameExecK_eq

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (hsq : Squarefree n) : framesExecK hsq = framesExec hsq :=
  funext fun s => frameExecK_eq hsq s
end TunnellMap.RecordDA

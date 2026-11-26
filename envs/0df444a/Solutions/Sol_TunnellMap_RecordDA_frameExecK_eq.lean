-- Prove2me | solution 1 for TunnellMap.RecordDA.frameExecK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:09:19.070793+00:00
-- url     : https://prove2.me/submissions/c5e7babf-6f7a-4961-9f4c-61608837fb6a

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
import Theorems.Thm_TunnellMap_reduceFrameK_eq


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (hsq : Squarefree n) (s : BResidual n) :
    frameExecK hsq s = frameExec hsq s := reduceFrameK_eq _
end TunnellMap.RecordDA

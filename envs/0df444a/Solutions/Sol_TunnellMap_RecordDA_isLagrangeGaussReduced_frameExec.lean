-- Prove2me | solution 1 for TunnellMap.RecordDA.isLagrangeGaussReduced_frameExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:30:23.70182+00:00
-- url     : https://prove2.me/submissions/07144c44-a0dc-4251-a8f4-38b042898a13

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_isLagrangeGaussReduced_reduceFrame


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (hsq : Squarefree n) (s : BResidual n) :
    IsLagrangeGaussReduced (frameExec hsq s) :=
  isLagrangeGaussReduced_reduceFrame _
end TunnellMap.RecordDA

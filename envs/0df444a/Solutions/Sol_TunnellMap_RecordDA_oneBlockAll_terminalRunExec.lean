-- Prove2me | solution 1 for TunnellMap.RecordDA.oneBlockAll_terminalRunExec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:31:51.81815+00:00
-- url     : https://prove2.me/submissions/5919365f-8cd0-4c10-922a-e52954b3a3ce

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_RecordDA_oneBlockAll_initial
import Theorems.Thm_TunnellMap_RecordDA_oneBlockAll_run


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) :
    OneBlockAll frames (terminalRunExec frames) :=
  oneBlockAll_run frames (oneBlockAll_initial frames (sourceRosterExec n))
end TunnellMap.RecordDA

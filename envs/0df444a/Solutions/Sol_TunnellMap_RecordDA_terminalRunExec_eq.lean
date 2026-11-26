-- Prove2me | solution 1 for TunnellMap.RecordDA.terminalRunExec_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:49:06.46598+00:00
-- url     : https://prove2.me/submissions/9c821470-bd8c-4200-9c3a-bcf1a9a2aff0

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
import Theorems.Thm_TunnellMap_sourceRosterExec_eq_sourceRoster


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
namespace TunnellMap.RecordDA
theorem _root_.solution [Fintype (BOddRep n)] (frames : FrameFamily n) :
    terminalRunExec frames = terminalRun frames := by
  rw [terminalRunExec, terminalRun, sourceRosterExec_eq_sourceRoster]
end TunnellMap.RecordDA

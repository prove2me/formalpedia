-- Prove2me | solution 1 for TunnellMap.RecordDA.oneBlockAll_terminalRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:27:56.727935+00:00
-- url     : https://prove2.me/submissions/7101ec46-9573-42b9-bfc9-0e22ee792c8b

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Theorems.Thm_TunnellMap_RecordDA_oneBlockAll_initial
import Theorems.Thm_TunnellMap_RecordDA_oneBlockAll_run


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
omit [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (frames : FrameFamily n) :
    OneBlockAll frames (terminalRun frames) :=
  oneBlockAll_run frames (oneBlockAll_initial frames (sourceRoster n))
end TunnellMap.RecordDA

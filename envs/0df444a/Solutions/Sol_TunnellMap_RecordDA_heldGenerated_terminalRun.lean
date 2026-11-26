-- Prove2me | solution 1 for TunnellMap.RecordDA.heldGenerated_terminalRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:38:14.431499+00:00
-- url     : https://prove2.me/submissions/45b629f2-1cb6-4498-8365-49eca65905db

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_RecordSign
import Definitions.Def_TunnellMap_InverseByRerun
import Theorems.Thm_TunnellMap_RecordDA_heldGenerated_initial
import Theorems.Thm_TunnellMap_RecordDA_heldGenerated_run

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) : HeldGenerated frames (terminalRun frames) :=
  heldGenerated_run hn hnpos frames (sim_initial hnpos frames sourceRoster_canon)
    (heldGenerated_initial frames (sourceRoster n))
end TunnellMap.RecordDA

-- Prove2me | solution 1 for TunnellMap.RecordDA.sim_terminalRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:14:26.543232+00:00
-- url     : https://prove2.me/submissions/c203e337-0162-4401-b68c-bc944fbc155a

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n) (frames : FrameFamily n) :
    Sim hnpos frames (terminalRun frames) :=
  (sim_run hn hnpos frames (sim_initial hnpos frames sourceRoster_canon)).1
end TunnellMap.RecordDA

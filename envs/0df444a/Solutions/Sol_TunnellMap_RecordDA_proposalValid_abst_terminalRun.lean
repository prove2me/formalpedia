-- Prove2me | solution 1 for TunnellMap.RecordDA.proposalValid_abst_terminalRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:35.570665+00:00
-- url     : https://prove2.me/submissions/b9b41fc4-ad48-4079-b01a-2530066fb522

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_proposalValid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_run


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n) :
    (abst hn hnpos frames (terminalRun frames)).ProposalValid
      (residualOrbitRanking hnpos) := by
  rw [abst_terminalRun]
  exact DAState.proposalValid_run _ _ (DAState.initial_proposalValid _ _)
end TunnellMap.RecordDA

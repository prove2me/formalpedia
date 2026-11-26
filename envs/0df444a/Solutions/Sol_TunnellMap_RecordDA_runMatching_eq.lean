-- Prove2me | solution 1 for TunnellMap.RecordDA.runMatching_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:27.798038+00:00
-- url     : https://prove2.me/submissions/5b675e7e-94ab-4782-beac-52612e55c5fc

import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Theorems.Thm_TunnellMap_RecordDA_proposalValid_abst_terminalRun
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_stable
import Theorems.Thm_TunnellMap_residualOrbitMatching_unique


set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen GloballyRanked
variable {n : ℤ}
variable [Fintype (BOddRep n)] [Fintype (ARep n)]
namespace TunnellMap.RecordDA
theorem _root_.solution (hn : Odd n) (hnpos : 0 < n)
    (frames : FrameFamily n)
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    runMatching hn hnpos frames hcard = residualOrbitMatching hnpos hcard :=
  residualOrbitMatching_unique hnpos hcard _
    (DAState.matchingOfTerminal_stable _ hcard _
      (valid_abst_terminalRun hn hnpos frames)
      (proposalValid_abst_terminalRun hn hnpos frames) _)
end TunnellMap.RecordDA

-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.matchingOfTerminal_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:40.575019+00:00
-- url     : https://prove2.me/submissions/ed9a404c-6cef-4f47-85b3-c54c3ebc1cf5

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_certificate
import Theorems.Thm_TunnellMap_GloballyRanked_stable_of_deferredAcceptanceCertificate


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.Stable (matchingOfTerminal I hcard st hv hqueue) :=
  I.stable_of_deferredAcceptanceCertificate _
    (matchingOfTerminal_certificate I hcard st hv hp hqueue)
end TunnellMap.GloballyRanked.DAState

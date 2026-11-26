-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.runCost_generatorAdvances_eq_proposalSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:49:19.265737+00:00
-- url     : https://prove2.me/submissions/c93067c5-b7c5-4326-bb1b-db66fa63bc36

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_advances_add_remaining

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I := by
  have haccount := runCost_advances_add_remaining I st
  have hle : (st.run I).remaining I ≤ st.remaining I := by omega
  unfold proposalSteps
  omega
end TunnellMap.GloballyRanked.DAState

-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_stable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:43:05.230727+00:00
-- url     : https://prove2.me/submissions/1ae6876a-a572-4a11-b71c-5bfe36a74aea

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_proposalValid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_run
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_stable
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_valid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_queue_nil
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run


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
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    I.Stable (deferredAcceptanceMatching I hcard sourceOrder hnodup hcomplete) := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let hp₀ : st₀.ProposalValid I := initial_proposalValid I sourceOrder
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hp : st.ProposalValid I := proposalValid_run I st₀ hp₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  change I.Stable (matchingOfTerminal I hcard st hv hqueue)
  exact matchingOfTerminal_stable I hcard st hv hp hqueue
end TunnellMap.GloballyRanked.DAState

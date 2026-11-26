-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.run_proposalSteps_le_triangular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:34:51.126293+00:00
-- url     : https://prove2.me/submissions/4d1efeaf-8b37-473d-80e8-766a7a054136

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_assignedLast
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_run
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalSteps_initial_eq_terminalCursorTotal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_terminal_cursorTotal_eq_proposalCount_sum
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_proposalValid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_valid
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_stable
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_run
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_queue_nil
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run
import Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_total_le_triangular


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
    (initial I sourceOrder).proposalSteps I ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by
  let st₀ := initial I sourceOrder
  let hv₀ : st₀.Valid I := initial_valid I sourceOrder hnodup hcomplete
  let hl₀ : st₀.AssignedLast I := initial_assignedLast I sourceOrder
  let st := st₀.run I
  let hv : st.Valid I := valid_run I st₀ hv₀
  let hl : st.AssignedLast I := assignedLast_run I st₀ hv₀ hl₀
  let hqueue : st.queue = [] := run_queue_nil I hcard st₀ hv₀
  let M := matchingOfTerminal I hcard st hv hqueue
  have hsteps : st₀.proposalSteps I = st.cursorTotal I :=
    proposalSteps_initial_eq_terminalCursorTotal I sourceOrder
  have htotal : st.cursorTotal I = ∑ s : S, I.proposalCount M s :=
    terminal_cursorTotal_eq_proposalCount_sum I hcard st hv hl hqueue
  rw [hsteps, htotal]
  exact I.proposalCount_total_le_triangular M
    (matchingOfTerminal_stable I hcard st hv
      (proposalValid_run I st₀ (initial_proposalValid I sourceOrder)) hqueue)
end TunnellMap.GloballyRanked.DAState

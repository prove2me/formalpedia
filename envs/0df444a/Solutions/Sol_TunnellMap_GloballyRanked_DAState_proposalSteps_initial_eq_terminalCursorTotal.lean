-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.proposalSteps_initial_eq_terminalCursorTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:46:24.151922+00:00
-- url     : https://prove2.me/submissions/3f73d19d-d5d5-43e5-9c23-567931fcf77b

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_cursorTotal_add_remaining
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_get_preferenceIndex
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
attribute [local simp] TunnellMap.GloballyRanked.get_preferenceIndex
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_at_left
attribute [local simp] TunnellMap.GloballyRanked.insertEquiv_symm_at_right
attribute [local simp] TunnellMap.GloballyRanked.length_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.mem_preferenceList



set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution
    (sourceOrder : List S) :
    (initial I sourceOrder).proposalSteps I =
      ((initial I sourceOrder).run I).cursorTotal I := by
  have hinitial := cursorTotal_add_remaining I (initial I sourceOrder)
  have hterminal := cursorTotal_add_remaining I ((initial I sourceOrder).run I)
  have hzero : (initial I sourceOrder).cursorTotal I = 0 := by
    simp [initial, cursorTotal]
  have hinitRemaining : (initial I sourceOrder).remaining I =
      Fintype.card S * Fintype.card T := by
    omega
  unfold proposalSteps
  rw [hinitRemaining]
  omega
end TunnellMap.GloballyRanked.DAState

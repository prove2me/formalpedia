-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.assignedLast_acceptEmpty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:42:49.793797+00:00
-- url     : https://prove2.me/submissions/fea8fb9b-cb56-47ac-a1fc-4681355fe5b4

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
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
theorem _root_.solution (st : I.DAState)
    (hlast : st.AssignedLast I) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).AssignedLast I := by
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    have ht : st.nextTarget I s h = t := by
      simpa [acceptEmpty] using hassigned
    subst t
    constructor
    · simp [acceptEmpty, advancedCursor]
    · simpa [acceptEmpty, advancedCursor] using
        nextTarget_getElem? I st s h
  · have hold : st.assigned x = some t := by
      simpa [acceptEmpty, hxs] using hassigned
    have hlastOld := hlast x t hold
    simpa [acceptEmpty, advancedCursor, hxs] using hlastOld
end TunnellMap.GloballyRanked.DAState

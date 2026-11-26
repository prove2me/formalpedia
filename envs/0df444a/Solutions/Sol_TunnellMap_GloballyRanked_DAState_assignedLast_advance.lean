-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.assignedLast_advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:45:57.633941+00:00
-- url     : https://prove2.me/submissions/91dd36f6-3faf-4221-b942-a2359bcdf560

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_acceptEmpty
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_rejectProposal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_replaceHeld
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
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).AssignedLast I := by
  simp only [advance]
  split
  · exact assignedLast_acceptEmpty I st hlast s rest h
  · split
    · apply assignedLast_replaceHeld I st hv hlast s rest hqueue h
      assumption
    · exact assignedLast_rejectProposal I st hv hlast s rest hqueue h
end TunnellMap.GloballyRanked.DAState

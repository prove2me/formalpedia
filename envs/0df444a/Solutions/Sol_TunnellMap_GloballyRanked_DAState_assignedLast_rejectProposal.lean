-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.assignedLast_rejectProposal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:43:56.56714+00:00
-- url     : https://prove2.me/submissions/b701991d-2e98-44db-b3b6-0b3841ec2295

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
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
    (st.rejectProposal I s rest h).AssignedLast I := by
  have hsMem : s ∈ st.queue := by simp [hqueue]
  have hsFree : st.assigned s = none :=
    (hv.queued_iff_unassigned s).mp hsMem
  intro x t hassigned
  by_cases hxs : x = s
  · subst x
    simp [rejectProposal, hsFree] at hassigned
  · have hlastOld := hlast x t hassigned
    simpa [rejectProposal, advancedCursor, hxs] using hlastOld
end TunnellMap.GloballyRanked.DAState

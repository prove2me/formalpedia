-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.proposalValid_advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:27.992802+00:00
-- url     : https://prove2.me/submissions/86e05281-ff9e-4d08-a15e-a7138257cc97

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_acceptEmpty
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_rejectProposal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_replaceHeld
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
attribute [local simp] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
attribute [local simp] TunnellMap.GloballyRanked.finalPartner_mem_proposalTargets
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
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).ProposalValid I := by
  simp only [advance]
  split
  · apply proposalValid_acceptEmpty I st hv s rest h
    assumption
  · split
    · apply proposalValid_replaceHeld I st hv s rest h
      · assumption
      · assumption
    · apply proposalValid_rejectProposal I st hv s rest h
      · assumption
      · assumption
end TunnellMap.GloballyRanked.DAState

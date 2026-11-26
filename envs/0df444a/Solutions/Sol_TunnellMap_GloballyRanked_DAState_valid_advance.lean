-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:43.893575+00:00
-- url     : https://prove2.me/submissions/c4456040-6965-4516-94bd-b508abac9a41

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_acceptEmpty
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_rejectProposal
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_replaceHeld
import Theorems.Thm_TunnellMap_GloballyRanked_finalPartner_mem_proposalTargets
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_at_left
import Theorems.Thm_TunnellMap_GloballyRanked_insertEquiv_symm_at_right
import Theorems.Thm_TunnellMap_GloballyRanked_length_preferenceList
import Theorems.Thm_TunnellMap_GloballyRanked_mem_preferenceList
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
theorem _root_.solution (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).Valid I := by
  simp only [advance]
  split
  · apply valid_acceptEmpty I st hv s rest hqueue h
    assumption
  · split
    · apply valid_replaceHeld I st hv s rest hqueue h
      assumption
    · apply valid_rejectProposal I st hv s rest hqueue h
      assumption
end TunnellMap.GloballyRanked.DAState

-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.runCost_component_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:47:53.677336+00:00
-- url     : https://prove2.me/submissions/eb75247d-9811-4183-927a-d9943a9dd6cf

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_oneStepCost_bounds
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
theorem _root_.solution (st : I.DAState) :
    (st.runCost I).keyComparisons ≤ (st.runCost I).generatorAdvances ∧
      (st.runCost I).queueOperations ≤
        2 * (st.runCost I).generatorAdvances ∧
      (st.runCost I).assignmentWrites ≤
        3 * (st.runCost I).generatorAdvances := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [runCost.eq_1, hstep]
      simp [ControlCost.zero]
  | case2 st st' hstep ih =>
      rw [runCost.eq_1, hstep]
      obtain ⟨hadvance, hkey, hqueue, hassign⟩ :=
        oneStepCost_bounds I st st' hstep
      simp only [ControlCost.add]
      omega
end TunnellMap.GloballyRanked.DAState

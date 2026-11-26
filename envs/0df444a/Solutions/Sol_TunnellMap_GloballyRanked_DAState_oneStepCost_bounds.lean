-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.oneStepCost_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:43.987264+00:00
-- url     : https://prove2.me/submissions/e9c9dc5d-ff6d-49f5-9d47-ea9dc47e2a34

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
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
theorem _root_.solution (st st' : I.DAState)
    (hstep : st.step I = some st') :
    (st.oneStepCost I).generatorAdvances = 1 ∧
      (st.oneStepCost I).keyComparisons ≤ 1 ∧
      (st.oneStepCost I).queueOperations ≤ 2 ∧
      (st.oneStepCost I).assignmentWrites ≤ 3 := by
  cases hqueue : st.queue with
  | nil => simp [step, oneStepCost, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp only [step, hqueue, hcur, dite_true] at hstep
        simp only [oneStepCost, hqueue, hcur, dite_true]
        split
        · simp
        · split <;> simp
      · simp [step, hqueue, hcur] at hstep
end TunnellMap.GloballyRanked.DAState

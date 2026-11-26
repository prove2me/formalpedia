-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.runCost_linear_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:35:39.698633+00:00
-- url     : https://prove2.me/submissions/7dc5da42-532a-4ed5-9525-e36a2ffafb1f

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_component_bounds
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_generatorAdvances_eq_proposalSteps

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I ∧
      (st.runCost I).keyComparisons ≤ st.proposalSteps I ∧
      (st.runCost I).queueOperations ≤ 2 * st.proposalSteps I ∧
      (st.runCost I).assignmentWrites ≤ 3 * st.proposalSteps I := by
  have hcomponents := runCost_component_bounds I st
  have hadvances := runCost_generatorAdvances_eq_proposalSteps I st
  rw [hadvances] at hcomponents
  exact ⟨hadvances, hcomponents⟩
end TunnellMap.GloballyRanked.DAState

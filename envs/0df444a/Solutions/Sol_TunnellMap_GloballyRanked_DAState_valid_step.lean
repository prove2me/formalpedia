-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:52.620914+00:00
-- url     : https://prove2.me/submissions/48a3d1d2-80ee-4900-8306-0c9a17100b2a

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_advance
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
theorem _root_.solution (st st' : I.DAState) (hv : st.Valid I)
    (hstep : st.step I = some st') : st'.Valid I := by
  cases hqueue : st.queue with
  | nil => simp [step, hqueue] at hstep
  | cons s rest =>
      by_cases hcur : st.cursor s < Fintype.card T
      · simp [step, hqueue, hcur] at hstep
        subst st'
        exact valid_advance I st hv s rest hqueue hcur
      · simp [step, hqueue, hcur] at hstep
end TunnellMap.GloballyRanked.DAState

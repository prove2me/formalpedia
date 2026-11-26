-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.step_eq_none_iff_queue_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:11:52.078796+00:00
-- url     : https://prove2.me/submissions/7f62d32f-bf7f-41c3-955f-ec19344c6d3e

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_queued_cursor_lt
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
theorem _root_.solution
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.step I = none ↔ st.queue = [] := by
  constructor
  · intro hstep
    cases hqueue : st.queue with
    | nil => rfl
    | cons s rest =>
        have hs : s ∈ st.queue := by simp [hqueue]
        have hcur := queued_cursor_lt I hcard st hv s hs
        simp [step, hqueue, hcur] at hstep
  · intro hqueue
    simp [step, hqueue]
end TunnellMap.GloballyRanked.DAState

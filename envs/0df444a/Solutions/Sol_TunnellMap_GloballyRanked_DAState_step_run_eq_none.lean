-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.step_run_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:06:20.458603+00:00
-- url     : https://prove2.me/submissions/75f20d3f-fc1d-4604-895d-efbb3bfb9bdd

import Definitions.Def_TunnellMap_DeferredAcceptance
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState) : (st.run I).step I = none := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hstep
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih
end TunnellMap.GloballyRanked.DAState

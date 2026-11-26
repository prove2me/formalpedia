-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.valid_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:44.499833+00:00
-- url     : https://prove2.me/submissions/f9ccc088-8f76-4181-b7cb-559d2301add7

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_step

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState) (hv : st.Valid I) :
    (st.run I).Valid I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hv
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (valid_step I st st' hv hstep)
end TunnellMap.GloballyRanked.DAState

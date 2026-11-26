-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.assignedLast_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:51:22.360438+00:00
-- url     : https://prove2.me/submissions/02cb8d8c-67ae-42f3-b1e9-ea4464c5e0d4

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_step
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_step


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I) :
    (st.run I).AssignedLast I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hlast
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (valid_step I st st' hv hstep)
        (assignedLast_step I st st' hv hlast hstep)
end TunnellMap.GloballyRanked.DAState

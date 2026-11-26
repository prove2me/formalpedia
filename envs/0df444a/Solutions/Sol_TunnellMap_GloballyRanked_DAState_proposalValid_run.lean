-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.proposalValid_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:56.447168+00:00
-- url     : https://prove2.me/submissions/f6ced3d6-393c-4a5b-9098-71b55d438603

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_step

set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (st : I.DAState) (hv : st.ProposalValid I) :
    (st.run I).ProposalValid I := by
  induction st using run.induct I with
  | case1 st hstep =>
      rw [run.eq_1, hstep]
      exact hv
  | case2 st st' hstep ih =>
      rw [run.eq_1, hstep]
      exact ih (proposalValid_step I st st' hv hstep)
end TunnellMap.GloballyRanked.DAState

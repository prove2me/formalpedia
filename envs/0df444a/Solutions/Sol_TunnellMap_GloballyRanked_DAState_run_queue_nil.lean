-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.run_queue_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:52.339321+00:00
-- url     : https://prove2.me/submissions/ecd715d1-a1f0-4c3d-ba3a-3c7cd64d3306

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_step_eq_none_iff_queue_nil
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_step_run_eq_none


set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)
namespace TunnellMap.GloballyRanked.DAState
theorem _root_.solution (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    (st.run I).queue = [] := by
  have hvrun := valid_run I st hv
  exact (step_eq_none_iff_queue_nil I hcard (st.run I) hvrun).mp
    (step_run_eq_none I st)
end TunnellMap.GloballyRanked.DAState

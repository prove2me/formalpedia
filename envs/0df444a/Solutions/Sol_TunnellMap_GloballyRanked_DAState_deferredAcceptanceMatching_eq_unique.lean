-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_eq_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:13.133089+00:00
-- url     : https://prove2.me/submissions/14b9ddf2-42dd-4785-9088-a09fe8a0a32a

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_stable
import Theorems.Thm_TunnellMap_GloballyRanked_exists_unique_stable


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
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    deferredAcceptanceMatching I hcard sourceOrder hnodup hcomplete =
      Classical.choose (I.exists_unique_stable hcard) := by
  classical
  exact (Classical.choose_spec (I.exists_unique_stable hcard)).2 _
    (deferredAcceptanceMatching_stable I hcard sourceOrder hnodup hcomplete)
end TunnellMap.GloballyRanked.DAState

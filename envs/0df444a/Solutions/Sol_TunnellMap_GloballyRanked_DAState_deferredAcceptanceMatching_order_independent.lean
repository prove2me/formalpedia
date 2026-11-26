-- Prove2me | solution 1 for TunnellMap.GloballyRanked.DAState.deferredAcceptanceMatching_order_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:57:14.423633+00:00
-- url     : https://prove2.me/submissions/853d495c-0744-4454-ba62-c33d1903c1dc

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_deferredAcceptanceMatching_eq_unique

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
    (order₁ order₂ : List S)
    (hnodup₁ : order₁.Nodup) (hnodup₂ : order₂.Nodup)
    (hcomplete₁ : ∀ s, s ∈ order₁) (hcomplete₂ : ∀ s, s ∈ order₂) :
    deferredAcceptanceMatching I hcard order₁ hnodup₁ hcomplete₁ =
      deferredAcceptanceMatching I hcard order₂ hnodup₂ hcomplete₂ := by
  rw [deferredAcceptanceMatching_eq_unique I hcard order₁ hnodup₁ hcomplete₁,
    deferredAcceptanceMatching_eq_unique I hcard order₂ hnodup₂ hcomplete₂]
end TunnellMap.GloballyRanked.DAState

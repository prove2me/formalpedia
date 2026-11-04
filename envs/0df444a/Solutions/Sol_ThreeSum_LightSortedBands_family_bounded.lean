-- Prove2me | solution 1 for ThreeSum.LightSortedBands.family_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:31.239203+00:00
-- url     : https://prove2.me/submissions/54efc728-ed83-4403-87e9-44963e2dcfae

import Definitions.Def_Submission_ThreeSum_LightNormalize
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_Submission_ThreeSum_LightBandEnumeration
import Definitions.Def_Submission_ThreeSum_LightSortedBands

set_option autoImplicit false
open ThreeSum ThreeSum.LightSortedBands
open Light ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSortedBands
theorem _root_.solution {L original : List ℤ} {g U : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    (hU : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    LightBandEnumeration.Bounded
      (BandPartition.family (fun i => L.getD i 0) L.length g hg (getD_strict hs)) U := by
  have hget (i : ℕ) (hi : i < L.length) : |L.getD i 0| ≤ (U : ℤ) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hU _ ((hmem _).mp (List.getElem_mem hi))
  intro i hi
  exact ⟨hget _ (start_lt hg hi),hget _ (stop_sub_one_lt hg hi)⟩
end ThreeSum.LightSortedBands

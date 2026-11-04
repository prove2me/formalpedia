-- Prove2me | solution 1 for ThreeSum.LightNormalize.dedup_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:28:01.329145+00:00
-- url     : https://prove2.me/submissions/bfdabb1b-d05a-4053-b119-c1240c4eedb9

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_MergeSort
import Mathlib.Data.List.Dedup
import Definitions.Def_Submission_ThreeSum_LightNormalize

set_option autoImplicit false
open ThreeSum ThreeSum.LightNormalize
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightNormalize
theorem _root_.solution {L : List ℤ} (hs : L.Pairwise (· ≤ ·)) :
    L.dedup.Pairwise (· < ·) := by
  have hle := hs.sublist (List.dedup_sublist L)
  have hne := List.nodup_dedup L
  exact (List.pairwise_and_iff.mpr ⟨hle,hne⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)
end ThreeSum.LightNormalize

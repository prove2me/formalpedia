-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.decodedWeight_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:18.476283+00:00
-- url     : https://prove2.me/submissions/55242438-a882-4047-8c7d-aca50c4922b8

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Mathlib.Data.List.Range
import Definitions.Def_Submission_ThreeSum_WeightEnumeration
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.WeightEnumeration
open LocalHashMoments
variable {ι K : Type*} [DecidableEq ι] [NatCast K]
namespace ThreeSum.WeightEnumeration
theorem _root_.solution (L p k : ℕ) (i : Fin L × Bool) :
    (decodedWeight (K := ZMod p) L p k i).val = digit p (2*L) k (coordinateIndex i) := by
  simp [decodedWeight,digit,ZMod.val_natCast]
end ThreeSum.WeightEnumeration

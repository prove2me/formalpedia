-- Prove2me | solution 1 for ThreeSum.WeightEnumeration.getElem_allWeights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:19.484955+00:00
-- url     : https://prove2.me/submissions/20f3c233-0444-4747-842e-9925ea18c25d

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
theorem _root_.solution (L p k : ℕ) (hk : k < p^(2*L)) :
    (allWeights L ((List.range p).map (fun n : ℕ => (n : K))))[k]'(by
      rw [allWeights_length]; exact hk) = decodedWeight (K := K) L p k := by
  simp only [allWeights_eq_range,List.getElem_map,List.getElem_range]
end ThreeSum.WeightEnumeration

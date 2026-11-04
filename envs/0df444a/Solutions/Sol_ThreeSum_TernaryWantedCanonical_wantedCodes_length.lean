-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonical.wantedCodes_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:30:48.485531+00:00
-- url     : https://prove2.me/submissions/c8ec7516-cc9c-4ab5-b3fc-dcd4d70931dc

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonical
theorem _root_.solution (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    (wantedCodes p raws digits j x code R).length=(wantedOutputs p raws j x).length := by
  simp [wantedCodes]
end ThreeSum.TernaryWantedCanonical

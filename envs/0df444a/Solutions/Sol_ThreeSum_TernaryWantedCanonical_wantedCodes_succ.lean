-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonical.wantedCodes_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:38.592457+00:00
-- url     : https://prove2.me/submissions/df97fe1d-baa8-4f17-a804-0b705ebc692e

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonical
theorem _root_.solution (p : ℤ) (raws : List ℤ) (digits : List ℕ)
    (j : ℕ) (x : ℤ) (code R : ℕ) :
    wantedCodes p raws digits (j+1) x code R = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws digits j ((x-raws.getD i 0)/p) (code*R+digits.getD i 0) R := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]
end ThreeSum.TernaryWantedCanonical

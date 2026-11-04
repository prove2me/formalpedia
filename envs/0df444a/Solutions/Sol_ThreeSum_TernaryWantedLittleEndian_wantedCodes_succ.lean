-- Prove2me | solution 1 for ThreeSum.TernaryWantedLittleEndian.wantedCodes_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:15.957628+00:00
-- url     : https://prove2.me/submissions/7eb2e841-711a-4df2-ae44-d71f59356838

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


attribute [local simp] ThreeSum.TernaryWantedLittleEndian.wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedLittleEndian
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedLittleEndian
theorem _root_.solution (p : ℤ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ)
    (x : ℤ) (R S code scale mapCode mapScale : ℕ) :
    wantedCodes p raws words maps (j+1) x R S code scale mapCode mapScale =
      (localBucket p raws x).flatMap fun i => wantedCodes p raws words maps j
        ((x-raws.getD i 0)/p) R S (code+scale*words.getD i 0) (scale*R)
          (mapCode+mapScale*maps.getD i 0) (mapScale*S) := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]
end ThreeSum.TernaryWantedLittleEndian

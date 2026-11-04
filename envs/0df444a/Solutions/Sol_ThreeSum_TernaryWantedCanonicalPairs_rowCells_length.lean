-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:05.734383+00:00
-- url     : https://prove2.me/submissions/046adbd6-604b-4544-858b-19dabf8f7271

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryAddresses.codes_length
attribute [local simp] ThreeSum.TernaryEnumeration.mem_digits
attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonicalPairs
theorem _root_.solution (original : ℕ) (codes : List (ℕ × ℕ)) :
    (rowCells original codes).length=3*codes.length := by
  induction codes with
  | nil => simp [rowCells]
  | cons code codes ih => simp only [rowCells,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *; omega
end ThreeSum.TernaryWantedCanonicalPairs

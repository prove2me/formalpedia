-- Prove2me | solution 1 for ThreeSum.TernaryWantedLittleEndian.encode_reverse_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:40.470919+00:00
-- url     : https://prove2.me/submissions/083942b5-0f73-477d-b93b-d0116882d1e7

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_address_append
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
theorem _root_.solution (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (code scale : ℕ),
      encode digits (4^L) code scale is = code+scale*
        TernaryAddresses.code (is.reverse.flatMap localWords) := by
  intro is
  induction is with
  | nil => intro code scale; simp [encode,TernaryAddresses.code]
  | cons i is ih =>
    intro code scale
    rw [encode,ih,List.reverse_cons,List.flatMap_append,List.flatMap_singleton,
      TernaryWantedCanonicalPairs.address_append,hblocks,hdigits]
    ring
end ThreeSum.TernaryWantedLittleEndian

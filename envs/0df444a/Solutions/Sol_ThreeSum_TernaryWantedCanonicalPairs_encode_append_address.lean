-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonicalPairs.encode_append_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:24.934081+00:00
-- url     : https://prove2.me/submissions/a502db50-6ef8-4e97-802e-663fdd6f4a34

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Definitions.Def_Submission_ThreeSum_TernaryAddresses
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_rowCells_append
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_address_append
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
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_length
attribute [local simp] ThreeSum.TernaryWantedCanonicalPairs.rowCells_append

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonicalPairs
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonicalPairs
theorem _root_.solution (L : ℕ) (localWords : ℕ → List ℕ) (digits : List ℕ)
    (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i)) :
    ∀ (is : List ℕ) (preword : List ℕ),
      TernaryWantedCanonical.encode digits (4^L) (TernaryAddresses.code preword) is=
        TernaryAddresses.code (preword++blockWords localWords is) := by
  intro is
  induction is with
  | nil => intro preword; simp [TernaryWantedCanonical.encode,blockWords]
  | cons i is ih =>
    intro preword
    have hcode : TernaryAddresses.code preword*4^L+TernaryAddresses.code (localWords i) =
        TernaryAddresses.code (preword++localWords i) := by rw [address_append,hblocks]
    rw [TernaryWantedCanonical.encode,hdigits,hcode,ih]
    simp [blockWords,List.append_assoc]
end ThreeSum.TernaryWantedCanonicalPairs

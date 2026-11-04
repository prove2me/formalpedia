-- Prove2me | solution 1 for ThreeSum.TernaryWantedLittleEndian.mem_wantedCodes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:57:40.866839+00:00
-- url     : https://prove2.me/submissions/1328ff29-3098-478b-af95-2cccb40c5abc

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
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_wantedOutputs
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
theorem _root_.solution {p : ℤ} (hp : p ≠ 0) (raws : List ℤ) (words maps : List ℕ)
    (j : ℕ) (x : ℤ) (R S code scale mapCode mapScale w f : ℕ) :
    (w,f) ∈ wantedCodes p raws words maps j x R S code scale mapCode mapScale ↔
      ∃ is : List ℕ, is.length=j ∧ (∀ i ∈ is, i<raws.length) ∧
        p^j ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
        encode words R code scale is=w ∧ encode maps S mapCode mapScale is=f := by
  simp only [wantedCodes,List.mem_map,Prod.mk.injEq,mem_wantedOutputs p hp raws]
  aesop
end ThreeSum.TernaryWantedLittleEndian

-- Prove2me | solution 1 for ThreeSum.TernaryWantedLittleEndian.wanted_word_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:26.121587+00:00
-- url     : https://prove2.me/submissions/f4e59bd2-262d-470b-a85a-21dd44b54c41

import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonicalPairs
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_encode_reverse_address
import Theorems.Thm_ThreeSum_TernaryWantedLittleEndian_mem_wantedCodes
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_length
import Theorems.Thm_ThreeSum_TernaryEnumeration_mem_digits
import Theorems.Thm_ThreeSum_TernaryWantedCanonicalPairs_mem_wantedCodes
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
theorem _root_.solution {p : ℤ} (raws : List ℤ) (localWords : ℕ → List ℕ)
    (digits maps : List ℕ) (L J S : ℕ) (x : ℤ) (w f : ℕ)
    (hp : p ≠ 0) (hblocks : ∀ i, (localWords i).length=L)
    (hdigits : ∀ i, digits.getD i 0=TernaryAddresses.code (localWords i))
    (h : (w,f) ∈ wantedCodes p raws digits maps J x (4^L) S 0 1 0 1) :
    ∃ is : List ℕ, is.length=J ∧ (∀ i ∈ is, i<raws.length) ∧
      p^J ∣ x-Radix.positionalHash p (fun i => raws.getD i 0) is ∧
      w=TernaryAddresses.code (is.reverse.flatMap localWords) ∧
      f=encode maps S 0 1 is := by
  obtain ⟨is,hlen,hvalid,hdiv,hw,hf⟩ := (mem_wantedCodes hp raws digits maps J x (4^L) S 0 1 0 1 w f).mp h
  refine ⟨is,hlen,hvalid,hdiv,?_,hf.symm⟩
  rw [← hw,encode_reverse_address L localWords digits hblocks hdigits]
  simp
end ThreeSum.TernaryWantedLittleEndian

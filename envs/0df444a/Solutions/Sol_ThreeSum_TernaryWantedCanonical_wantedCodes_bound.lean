-- Prove2me | solution 1 for ThreeSum.TernaryWantedCanonical.wantedCodes_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:23.767914+00:00
-- url     : https://prove2.me/submissions/9c94bc6a-8688-4338-bb3e-a26e3552a530

import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryWantedCanonical
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedCanonical_codeLimit_child
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_length
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket


attribute [local simp] ThreeSum.TernaryWantedCanonical.wantedCodes_length

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedCanonical
open TernaryWantedRadix
namespace ThreeSum.TernaryWantedCanonical
theorem _root_.solution (p : ℤ) (raws : List ℤ) (digits : List ℕ) (R : ℕ)
    (hN : 1 ≤ raws.length) (hdigits : ∀ i < raws.length, digits.getD i 0 < R) :
    ∀ j x code z, z ∈ wantedCodes p raws digits j x code R →
      z ≤ codeLimit raws.length code R j := by
  intro j
  induction j with
  | zero => intro x code z hz; simp [wantedCodes,wantedOutputs,encode] at hz; subst z; simp [codeLimit]
  | succ j ih =>
    intro x code z hz
    rw [wantedCodes_succ] at hz
    obtain ⟨i,hi,hz⟩ := List.mem_flatMap.mp hz
    exact (ih _ _ _ hz).trans (codeLimit_child hN (hdigits i (mem_localBucket _ _ _ _ |>.mp hi).1))
end ThreeSum.TernaryWantedCanonical

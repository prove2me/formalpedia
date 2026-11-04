-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.wantedCodes_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:39.209736+00:00
-- url     : https://prove2.me/submissions/5fefa5b6-8774-4196-afd4-0f578f17dc61

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedCodes_succ
import Theorems.Thm_ThreeSum_TernaryWantedRadix_codeLimit_child
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


attribute [local simp] ThreeSum.TernaryWantedRadix.mem_localBucket

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) (hN : 1 ≤ raws.length) :
    ∀ j x code scale z, z ∈ wantedCodes p raws j x code scale →
      z ≤ codeLimit raws.length code scale j := by
  intro j
  induction j with
  | zero =>
    intro x code scale z hz
    have he : z = code := by simpa [wantedCodes,wantedOutputs,encode] using hz
    subst z
    simp [codeLimit]
  | succ j ih =>
    intro x code scale z hz
    rw [wantedCodes_succ] at hz
    obtain ⟨i,hi,hz⟩ := List.mem_flatMap.mp hz
    exact (ih _ _ _ _ hz).trans (codeLimit_child hN (mem_localBucket _ _ _ _ |>.mp hi).1)
end ThreeSum.TernaryWantedRadix

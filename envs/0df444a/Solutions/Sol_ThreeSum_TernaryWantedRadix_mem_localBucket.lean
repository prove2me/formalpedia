-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.mem_localBucket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:22:03.172101+00:00
-- url     : https://prove2.me/submissions/e08ef499-dc69-4bf4-9f08-978ce1692d5b

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedRadix
open Finset
namespace ThreeSum.TernaryWantedRadix
theorem _root_.solution (p : ℤ) (raws : List ℤ) (x : ℤ) (i : ℕ) :
    i ∈ localBucket p raws x ↔ i < raws.length ∧ p ∣ x-raws.getD i 0 := by
  simp [localBucket]
end ThreeSum.TernaryWantedRadix

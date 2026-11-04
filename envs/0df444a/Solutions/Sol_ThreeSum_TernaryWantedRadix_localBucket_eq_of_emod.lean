-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.localBucket_eq_of_emod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:09.433399+00:00
-- url     : https://prove2.me/submissions/1fc18558-624c-4b67-8dd1-4f1b5ff9ac61

import Definitions.Def_Submission_ThreeSum_Radix
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Theorems.Thm_ThreeSum_TernaryWantedRadix_mem_localBucket
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
theorem _root_.solution {p : ℤ} (raws : List ℤ) {x y : ℤ} (h : x%p = y%p) :
    localBucket p raws x = localBucket p raws y := by
  unfold localBucket
  congr 1
  funext i
  apply decide_eq_decide.mpr
  simp only [Int.dvd_iff_emod_eq_zero,Int.sub_emod,Int.emod_emod,h]
end ThreeSum.TernaryWantedRadix

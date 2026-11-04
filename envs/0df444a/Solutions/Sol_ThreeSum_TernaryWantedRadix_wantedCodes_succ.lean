-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.wantedCodes_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:59.553202+00:00
-- url     : https://prove2.me/submissions/56edde1c-5c4e-4e18-99cc-5fa9b0ef7439

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
theorem _root_.solution (p : ℤ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ) :
    wantedCodes p raws (j+1) x code scale = (localBucket p raws x).flatMap fun i =>
      wantedCodes p raws j ((x-raws.getD i 0)/p) (code+scale*i) (scale*raws.length) := by
  simp [wantedCodes,wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,encode]
end ThreeSum.TernaryWantedRadix

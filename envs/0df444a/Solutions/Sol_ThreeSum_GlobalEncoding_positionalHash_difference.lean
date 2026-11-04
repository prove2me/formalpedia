-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.positionalHash_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:20:56.022146+00:00
-- url     : https://prove2.me/submissions/b509c80a-1db8-4e7e-a189-368fa18c7f68

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_blockKey_choice
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.GlobalEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments
namespace ThreeSum.GlobalEncoding
theorem _root_.solution {h : ℕ} (xs : List (RetainedChoice h)) :
    Radix.positionalHash (localPrime h) rawRight xs -
      Radix.positionalHash (localPrime h) rawLeft xs =
        Radix.positionalHash (localPrime h) blockKey (xs.map blockOfChoice) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, Radix.positionalHash, blockKey_choice]
      rw [← ih]
      ring
end ThreeSum.GlobalEncoding

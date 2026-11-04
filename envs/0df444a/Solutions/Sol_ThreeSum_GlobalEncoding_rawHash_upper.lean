-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.rawHash_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:09.432978+00:00
-- url     : https://prove2.me/submissions/1bfa2473-496c-447f-aa4f-a467a5a272c0

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
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
theorem _root_.solution {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    rawHash w s ≤ (L : ℤ) * (localPrime h - 1) := by
  calc
    rawHash w s ≤ ∑ _i : Fin L, ((localPrime h : ℤ) - 1) := by
      unfold rawHash
      apply Finset.sum_le_sum
      intro i _
      have hi : ((w (i, s i)).val : ℤ) < (localPrime h : ℤ) := by
        exact_mod_cast (w (i, s i)).val_lt
      omega
    _ = _ := by simp [mul_sub]
end ThreeSum.GlobalEncoding

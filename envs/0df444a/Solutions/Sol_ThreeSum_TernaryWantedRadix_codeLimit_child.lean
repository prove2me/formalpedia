-- Prove2me | solution 1 for ThreeSum.TernaryWantedRadix.codeLimit_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:25:01.93896+00:00
-- url     : https://prove2.me/submissions/6d73adde-0aa0-4302-84ba-a2c8c0854fb1

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
theorem _root_.solution {N code scale j i : ℕ} (hN : 1 ≤ N) (hi : i < N) :
    codeLimit N (code+scale*i) (scale*N) j ≤ codeLimit N code scale (j+1) := by
  unfold codeLimit
  rw [pow_succ']
  have h : code+scale*i+scale*N ≤ (code+scale)*(2*N) := by nlinarith
  simpa [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_right ((2*N)^j) h
end ThreeSum.TernaryWantedRadix

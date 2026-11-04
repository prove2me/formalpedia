-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.rawHash_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:20.336941+00:00
-- url     : https://prove2.me/submissions/d69a5595-cfec-4843-96e7-94002898da0a

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalGraph_edge_data
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
theorem _root_.solution {h L k : ℕ} (w : Weight L (LocalField h))
    (e : Edge L k) :
    rawHash w (right e) - rawHash w (left e) = rawOutput w (output e) := by
  unfold rawHash rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [left, right, leftWord, rightWord, output]
end ThreeSum.GlobalEncoding

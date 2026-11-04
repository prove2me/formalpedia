-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.outputBlock_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:32.727788+00:00
-- url     : https://prove2.me/submissions/eb3a33f0-d7ca-4c59-82a4-a0641f2e2db1

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LayerCounts_vertices_card
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
theorem _root_.solution (h : ℕ) :
    Fintype.card (OutputBlock h) = scheduleSize h * outputCount (512 * h) h := by
  simp only [OutputBlock, Fintype.card_prod, Occurrence, Fintype.card_fin,
    Fintype.card_coe, LayerCounts.vertices_card, outputCount]
end ThreeSum.GlobalEncoding

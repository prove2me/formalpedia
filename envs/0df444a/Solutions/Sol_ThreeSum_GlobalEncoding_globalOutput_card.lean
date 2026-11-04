-- Prove2me | solution 1 for ThreeSum.GlobalEncoding.globalOutput_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:21.197481+00:00
-- url     : https://prove2.me/submissions/5b5a3d24-df80-4c5b-b38d-d264eff8acd3

import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_Radix
import Mathlib.Data.List.OfFn
import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Theorems.Thm_ThreeSum_GlobalEncoding_outputBlock_card
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
theorem _root_.solution (h J : ℕ) :
    Fintype.card (GlobalOutput h J) =
      scheduleSize h ^ J * outputCount (512 * h) h ^ J := by
  simp only [GlobalOutput, Fintype.card_fun, Fintype.card_fin, outputBlock_card, mul_pow]
end ThreeSum.GlobalEncoding

-- Prove2me | solution 1 for ThreeSum.OneHotMask.eval_rawLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:27.816681+00:00
-- url     : https://prove2.me/submissions/76b82b3b-2547-4fc0-ada8-05b1841c3955

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
import Theorems.Thm_ThreeSum_OneHotMask_extend_fin
import Theorems.Thm_ThreeSum_OneHotMask_mem_natPositions
import Theorems.Thm_ThreeSum_OneHotMask_eval_subsetMask
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.OneHotMask.extend_fin
attribute [local simp] ThreeSum.OneHotMask.mem_natPositions

set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.OneHotMask
theorem _root_.solution {h L : ℕ}
    (w : Weight L (LocalField h)) (s : Finset (Fin L)) :
    (eval (extend fun i => (w (i,false)).val) (extend fun i => (w (i,true)).val)
      L (subsetMask s) : ℤ) = GlobalEncoding.rawHash w (LocalGraph.leftWord s) := by
  rw [eval_subsetMask]
  unfold GlobalEncoding.rawHash
  push_cast
  apply sum_congr rfl
  intro i _
  by_cases hi : i ∈ s <;> simp [LocalGraph.leftWord, hi]
end ThreeSum.OneHotMask

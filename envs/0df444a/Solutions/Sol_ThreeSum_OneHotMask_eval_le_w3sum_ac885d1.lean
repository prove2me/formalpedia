-- Prove2me | solution 1 for ThreeSum.OneHotMask.eval_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:49.847107+00:00
-- url     : https://prove2.me/submissions/f7d243a8-f18a-4224-852f-3ef4257c6b1c

import Definitions.Def_Submission_ThreeSum_GlobalEncoding
import Definitions.Def_Submission_ThreeSum_MaskErase
import Definitions.Def_Submission_ThreeSum_OneHotMask
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



set_option autoImplicit false
open ThreeSum ThreeSum.OneHotMask
open Finset SubsetAddress LocalHashMoments
open scoped BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
namespace ThreeSum.OneHotMask
theorem _root_.solution {L m U : ℕ} {w0 w1 : ℕ → ℕ}
    (h0 : ∀ i < L, w0 i ≤ U) (h1 : ∀ i < L, w1 i ≤ U) :
    eval w0 w1 L m ≤ L*U := by
  induction L generalizing m with
  | zero => simp [eval]
  | succ L ih =>
    have h0L := h0 L (by omega)
    have h1L := h1 L (by omega)
    have h0' : ∀ i < L, w0 i ≤ U := fun i hi => h0 i (by omega)
    have h1' : ∀ i < L, w1 i ≤ U := fun i hi => h1 i (by omega)
    unfold eval
    split
    · have hh := ih (m := m) h0' h1'
      nlinarith
    · have hh := ih (m := m-2^L) h0' h1'
      nlinarith
end ThreeSum.OneHotMask

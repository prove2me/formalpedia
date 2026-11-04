-- Prove2me | solution 1 for ThreeSum.LightTernaryParallelBudget.radix_time_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:22.291979+00:00
-- url     : https://prove2.me/submissions/21073b8f-0abb-45e7-9b55-2edb6d797afe

import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelBudget
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryParallelBudget
namespace ThreeSum.LightTernaryParallelBudget
theorem _root_.solution (N : ℕ) (hN : 1≤N) : ∀ J,
    LightRadixKeys.time N J ≤ 500*(J+1)*(N^J+N+1) := by
  intro J
  induction J with
  | zero => simp [LightRadixKeys.time]; omega
  | succ J ih =>
    have hp : N^J ≤ N^(J+1) := Nat.pow_le_pow_right hN (by omega)
    have ht : 500*(J+1)*(N^J+N+1) ≤ 500*(J+1)*(N^(J+1)+N+1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hs : LightRadixRows.time N (N^J)+200 ≤ 500*(N^(J+1)+N+1) := by
      unfold LightRadixRows.time LightReportingAffine.time
      rw [pow_succ']
      nlinarith [Nat.zero_le (N*N^J)]
    rw [LightRadixKeys.time]
    have hadd := Nat.add_le_add (ih.trans ht) hs
    nlinarith
end ThreeSum.LightTernaryParallelBudget

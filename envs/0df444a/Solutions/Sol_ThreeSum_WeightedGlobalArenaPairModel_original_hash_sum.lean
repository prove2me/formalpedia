-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaPairModel.original_hash_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T18:04:31.647208+00:00
-- url     : https://prove2.me/submissions/c70cddcd-5877-4e2d-bcd9-e20e3f0f4401

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceModel
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairMoments
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPairModel
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_left_hash
import Theorems.Thm_ThreeSum_WeightedGlobalArenaPairModel_right_hash
import Theorems.Thm_ThreeSum_TernaryCoverLocal_hashes_add
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_target_row
import Theorems.Thm_ThreeSum_WeightedGlobalArenaSourceModel_original_rows


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaPairModel
open Finset TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps WeightedGlobalArenaSourceSetup
open WeightedGlobalNativePairMoments WeightedGlobalArenaSourceModel TernaryCoverLocal
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : WeightedGlobalGoodOutputCatalog.Output m) (I : Input)
variable {maps τ cap localQ I}
namespace ThreeSum.WeightedGlobalArenaPairModel
theorem _root_.solution {i : ℕ} (hi : i<(Host (r := r) maps τ cap localQ I).front.count)
    (x : Pair (Host (r := r) maps τ cap localQ I) i)
    (B C O : ℕ→Fin r→ZMod p)
    (hB : ∀ j<I.nB, I.leftInput j=(TernaryExtensionEncoding.coefficientCode (B j) : ℤ))
    (hC : ∀ j<I.nC, I.rightInput j=(TernaryExtensionEncoding.coefficientCode (C j) : ℤ))
    (hO : ∀ j<I.requesterCount, I.targets j=(TernaryExtensionEncoding.coefficientCode (O j) : ℤ)) :
    B x.val.1.1+C x.val.2.1=
      O (WeightedGlobalArenaQueryModel.descriptor maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1 := by
  obtain ⟨jL,hjL,hL⟩ := WeightedGlobalArenaSourceModel.original_rows maps cap I false B hB _ (left_mem x)
  obtain ⟨jR,hjR,hR⟩ := WeightedGlobalArenaSourceModel.original_rows maps cap I true C hC _ (right_mem x)
  have heL : jL=leftIndex x := Fin.ext hjL
  have heR : jR=rightIndex x := Fin.ext hjR
  rw [heL] at hL
  rw [heR] at hR
  have ho := WeightedGlobalArenaQueryModel.target_row maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩
    (O (WeightedGlobalArenaQueryModel.descriptor maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1)
    (hO _ (WeightedGlobalArenaQueryModel.descriptor_spec maps τ I.targets I.positions I.requesterCount ⟨i,hi⟩).1)
  rw [hL,hR,←ho]
  funext t
  change WeightedGlobalCanonicalSourceBank.nativeRow false maps cap (leftIndex x) t+
    WeightedGlobalCanonicalSourceBank.nativeRow true maps cap (rightIndex x) t=_
  rw [left_hash hi x t,right_hash hi x t,TernaryCoverLocal.hashes_add]
  rfl
end ThreeSum.WeightedGlobalArenaPairModel

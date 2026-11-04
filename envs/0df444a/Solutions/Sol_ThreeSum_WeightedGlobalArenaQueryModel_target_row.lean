-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaQueryModel.target_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T17:03:09.02207+00:00
-- url     : https://prove2.me/submissions/0fe66c99-226f-494a-8cf7-0b83c2245bb6

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryModel
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_Weighted_Global_TernaryArenaQueryNative
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_native_code
import Theorems.Thm_ThreeSum_LightTernaryCountFrontend_row
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_row
import Theorems.Thm_ThreeSum_WeightedGlobalArenaQueryModel_target_congruent
attribute [local simp] ThreeSum.LightTernaryCountFrontend.row
attribute [local simp] ThreeSum.LightWeightedCountFrontend.row



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaQueryModel
open TernaryJointType WeightedGlobalLocalParameters WeightedGlobalCoverGoodMaps TernaryCoverHashes
open TernaryWantedBatchIndex TernaryExtensionEncoding
variable {m p F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000
namespace ThreeSum.WeightedGlobalArenaQueryModel
theorem _root_.solution (maps : Fin F → Weight m p) (τ : ℕ) (targets : ℕ → ℤ)
    (positions : ℕ → ℕ) (n : ℕ) (j : Fin (queries (r := r) maps τ targets positions n).length)
    (row : Fin r → ZMod p)
    (htarget : targets (descriptor maps τ targets positions n j).1 = (coefficientCode row : ℤ)) :
    nativeRow maps τ targets positions n j = row := by
  have hd := target_congruent maps τ targets positions n j
  rw [htarget,native_code] at hd
  have hm : (coefficientCode row : ℤ) % (p : ℤ)^r =
      (coefficientCode (nativeRow maps τ targets positions n j) : ℤ) % (p : ℤ)^r :=
    Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.dvd_iff_emod_eq_zero.mp hd)
  have hl : (coefficientCode row : ℤ) < (p : ℤ)^r := by exact_mod_cast coefficientCode_lt row
  have hr : (coefficientCode (nativeRow maps τ targets positions n j) : ℤ) < (p : ℤ)^r := by
    exact_mod_cast coefficientCode_lt (nativeRow maps τ targets positions n j)
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hl,Int.emod_eq_of_lt (Int.natCast_nonneg _) hr] at hm
  exact coefficientCode_injective r (Int.ofNat_inj.mp hm.symm)
end ThreeSum.WeightedGlobalArenaQueryModel

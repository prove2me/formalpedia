-- Prove2me | solution 1 for ThreeSum.LightOriginalSurvivorPair.Resources.run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:25:30.980303+00:00
-- url     : https://prove2.me/submissions/39aa2b4a-6099-43b2-b1c0-006554148059

import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorPair
import Definitions.Def_Submission_ThreeSum_LightOriginalSurvivorResources
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LightBandLookup_program_meets
import Theorems.Thm_ThreeSum_LightColoredTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightDeletedTwoSum_flag_zero
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_bad_zero
import Theorems.Thm_ThreeSum_LightOriginalBucketFilter_good_zero
import Theorems.Thm_ThreeSum_LightOriginalCollisionCleanup_program_length
import Theorems.Thm_ThreeSum_LightOriginalSurvivorPair_program_meets
import Theorems.Thm_ThreeSum_LightOriginalSurvivorStage_program_meets
import Theorems.Thm_ThreeSum_LightReportingAffine_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_program_meets
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
import Theorems.Thm_ThreeSum_LightReportingGather_program_meets
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
attribute [local simp] ThreeSum.LightColoredTwoSum.flag_zero
attribute [local simp] ThreeSum.LightDeletedTwoSum.flag_zero
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.bad_zero
attribute [local simp] ThreeSum.LightOriginalBucketFilter.good_zero
attribute [local simp] ThreeSum.LightOriginalCollisionCleanup.program_length
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress LightOriginalCollisionCleanup
namespace ThreeSum.LightOriginalSurvivorPair
namespace Resources
theorem _root_.solution {c : Layout} {lim : Limits} {d U W : ℕ} {μ : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (R : Resources c lim d U W μ A B C keysB keysC) :
    Meets lim program 8 d c.args μ (time keysB keysC c.nA c.nB c.nC c.L)
      (fun ret ν => ret = (cleanupFlag A B C keysB keysC c.nA c.nB c.nC : ℤ) ∧
        Output ν keysB B c.nB c.outB c.valueB c.packedB c.lengthB ∧
        Output ν keysC C c.nC c.outC c.valueC c.packedC c.lengthC ∧ Kept μ ν c.outB ∧
          LightOriginalSurvivorStage.Above μ ν c.lengthC ∧ c.Unchanged keysB keysC μ ν) := by
  simpa only [Layout.args,Layout.Unchanged,cleanupFlag,Nat.cast_ite,Nat.cast_one] using
    program_meets μ A B C keysB keysC R.hw R.hA R.hB R.hC R.hkB R.hkC R.hhB R.hhC R.hp
      R.hB1 R.hB2 R.hB3 R.hBC R.hC1 R.hC2 R.hC3 R.hEnd R.hword R.hkeysB R.hkeysC
      R.hreadKB R.hreadKC R.hcountsB R.hcountsC R.hboundA R.hboundB R.hboundC R.hreadA R.hreadB R.hreadC
      R.hvalueWord R.hpowers R.hsortedB R.hsortedC R.hL R.hnB R.hnC R.hd
end Resources
end ThreeSum.LightOriginalSurvivorPair

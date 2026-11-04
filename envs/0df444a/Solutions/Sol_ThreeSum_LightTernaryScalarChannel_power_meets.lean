-- Prove2me | solution 1 for ThreeSum.LightTernaryScalarChannel.power_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:38:01.998696+00:00
-- url     : https://prove2.me/submissions/72f29802-a2c4-43fb-b930-9ebc3d76cb53

import Definitions.Def_Submission_ThreeSum_TernaryWeightChannels
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFiniteTable_meets
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightSignedFiniteTable_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_meets
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryWeightChannels_leftMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_powerCircuit_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_rightMoment_eval
import Theorems.Thm_ThreeSum_TernaryWeightChannels_scalarPower_eval
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.LightTernaryWeightedHistogram.total_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.TernaryBank.mem_bank
attribute [local simp] ThreeSum.TernaryBank.mem_lowerWords
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval



set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryScalarChannel
theorem _root_.solution {k p src n dst U : ℕ}
    (hmain : P[p]?=some (body (scalarPower k))) (μ : ℕ→ℤ) (f : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=f i) (hf : ∀ i<n, |f i|≤(U : ℤ))
    (hword : max (U : ℤ) ((scalarPower k).bound U)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (time (scalarPower k) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(f i)^k) ∧ SameOutside μ ν dst n) := by
  simpa only [scalarPower_eval] using meets (scalarPower k) hmain μ f hw hsrc hdst hsep hread hf hword
end ThreeSum.LightTernaryScalarChannel

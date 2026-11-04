-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentChannels.right_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:52.027615+00:00
-- url     : https://prove2.me/submissions/dd9cde18-e197-4b62-955b-9783667be7b2

import Definitions.Def_Submission_ThreeSum_LightTernaryScalarChannel
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentChannels
import Theorems.Thm_ThreeSum_LightTernaryMomentChannels_right_bound
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
import Theorems.Thm_ThreeSum_LightTernaryScalarChannel_meets
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
open ThreeSum ThreeSum.LightTernaryMomentChannels
open Light LightFixedArithmetic TernaryWeightChannels
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentChannels
theorem _root_.solution {k j p src n dst U : ℕ}
    (hmain : P[p]?=some (LightTernaryScalarChannel.body (rightMoment k j)))
    (μ : ℕ→ℤ) (C : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=C i) (hC : ∀ i<n, |C i|≤(U : ℤ))
    (hword : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word) :
    Meets lim P p d [src,n,dst] μ (LightTernaryScalarChannel.time (rightMoment k j) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(C i)^(k-j)) ∧ SameOutside μ ν dst n) := by
  have hh : max (U : ℤ) ((rightMoment k j).bound U)≤lim.word := by rwa [right_bound]
  simpa only [rightMoment_eval] using LightTernaryScalarChannel.meets (rightMoment k j)
    hmain μ C hw hsrc hdst hsep hread hC hh
end ThreeSum.LightTernaryMomentChannels

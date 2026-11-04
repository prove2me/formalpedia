-- Prove2me | solution 1 for ThreeSum.TernaryMomentMatrixInvariant.advance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:16.142731+00:00
-- url     : https://prove2.me/submissions/71374749-2960-477d-b8d2-965c6e5d03fc

import Definitions.Def_Submission_ThreeSum_TernaryMomentSchedule
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_Submission_ThreeSum_TernaryMomentMatrixInvariant
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_LightTernaryWeightedHistogram_total_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_TernaryBank_mem_bank
import Theorems.Thm_ThreeSum_TernaryBank_mem_lowerWords
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_append
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_cons
import Theorems.Thm_ThreeSum_TernaryMomentSchedule_aggregate_nil
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
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_append
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_cons
attribute [local simp] ThreeSum.TernaryMomentSchedule.aggregate_nil
attribute [local simp] ThreeSum.TernaryWeightChannels.leftMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.powerCircuit_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.rightMoment_eval
attribute [local simp] ThreeSum.TernaryWeightChannels.scalarPower_eval



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryMomentMatrixInvariant
open Light TernaryMomentSchedule
namespace ThreeSum.TernaryMomentMatrixInvariant
theorem _root_.solution {reference μ ν : ℕ→ℤ} {matrix count terms boundary k j : ℕ}
    (done : List (ℕ×ℕ)) (score : ℕ→ℕ→ℕ→ℤ)
    (hk : k<terms) (hwindow : matrix+terms*count≤boundary)
    (hI : Holds reference matrix count terms boundary done score μ)
    (hrow : ∀ i<count, ν (matrix+k*count+i)=aggregate done score k i+score k j i)
    (hkeep : ∀ a<boundary, (a<matrix+k*count ∨ matrix+k*count+count≤a) → ν a=μ a) :
    Holds reference matrix count terms boundary (done++[(k,j)]) score ν := by
  constructor
  · intro l hl i hi
    have hm := Nat.mul_le_mul_right count (show l+1≤terms by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have hbefore : matrix+l*count+i<boundary := by omega
    by_cases hkl : k=l
    · subst l
      simpa only [aggregate_append,aggregate_cons,aggregate_nil,ite_true,add_zero]
        using hrow i hi
    · have haway : matrix+l*count+i<matrix+k*count ∨
          matrix+k*count+count≤matrix+l*count+i := by
        by_cases hlk : l<k
        · left
          have hh := Nat.mul_le_mul_right count (show l+1≤k by omega)
          simp only [Nat.add_mul,one_mul] at hh
          omega
        · right
          have hh := Nat.mul_le_mul_right count (show k+1≤l by omega)
          simp only [Nat.add_mul,one_mul] at hh
          omega
      rw [hkeep _ hbefore haway,hI.1 l hl i hi]
      simp only [aggregate_append,aggregate_cons,aggregate_nil,hkl,ite_false,add_zero]
  · intro a ha haway
    have hm := Nat.mul_le_mul_right count (show k+1≤terms by omega)
    simp only [Nat.add_mul,one_mul] at hm
    have hr : a<matrix+k*count ∨ matrix+k*count+count≤a := by rcases haway with h|h <;> omega
    exact (hkeep a ha hr).trans (hI.2 a ha haway)
end ThreeSum.TernaryMomentMatrixInvariant

-- Prove2me | solution 1 for ThreeSum.LocalParameterBounds.space_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:16.431195+00:00
-- url     : https://prove2.me/submissions/82e583df-2a38-4651-a33f-f91c3a0f1837

import Definitions.Def_Submission_ThreeSum_LightLocalParameters
import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Theorems.Thm_ThreeSum_LocalParameterBounds_pow_pos
import Theorems.Thm_ThreeSum_LocalParameterBounds_root_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_width_bound
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightHistogram_count_zero
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
import Theorems.Thm_ThreeSum_WeightedScore_corrections_zero
import Theorems.Thm_ThreeSum_WeightedScore_remaining_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightHistogram.count_zero
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
attribute [local simp] ThreeSum.WeightedScore.corrections_zero
attribute [local simp] ThreeSum.WeightedScore.remaining_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LocalParameterBounds
open LocalCoverBounds
set_option maxHeartbeats 1000000
namespace ThreeSum.LocalParameterBounds
theorem _root_.solution (work h : ℕ) : LightLocalParameters.space work h ≤ work+envelope h := by
  have hw := width_bound h
  have hs : (512*h+1)^2 ≤ 2^(2*h+20) := by
    have hp := Nat.pow_le_pow_left hw 2
    simpa only [← pow_mul,show (h+10)*2 = 2*h+20 by omega] using hp
  have hw' : 512*h+1 ≤ 2^(2*h+20) := hw.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc : LightLocalCounts.space work h ≤ work+base h := by
    have hsum : (512*h+1)^2+(512*h+1) ≤ 2^(2*h+21) := by
      have he : (2 : ℕ)^(2*h+21) = 2*2^(2*h+20) := by
        rw [show 2*h+21 = (2*h+20)+1 by omega,pow_succ]
        omega
      rw [he]
      omega
    have hb : 2^(2*h+21) ≤ base h := Nat.pow_le_pow_right (by decide) (by omega)
    unfold LightLocalCounts.space LightPascal.tableSize
    omega
  have hr := root_bound h
  have hx := pow_pos (514*h)
  have hl := Nat.log_le_self 2 (4*rootCeiling (localThreshold h)+1)
  have hp : LightSelectedPrime.space work (localThreshold h) ≤ work+base h := by
    have hp' : LightSelectedPrime.space work (localThreshold h) ≤ work+2^(514*h+5) := by
      unfold LightSelectedPrime.space LightPrimePool.space
      rw [pow_add]
      norm_num
      omega
    exact hp'.trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)
  unfold LightLocalParameters.space
  exact (max_le hc hp).trans (Nat.add_le_add_left (Nat.pow_le_pow_right (by decide) (by omega)) work)
end ThreeSum.LocalParameterBounds

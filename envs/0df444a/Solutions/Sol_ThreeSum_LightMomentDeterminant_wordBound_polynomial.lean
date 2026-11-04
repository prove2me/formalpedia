-- Prove2me | solution 1 for ThreeSum.LightMomentDeterminant.wordBound_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:20.224146+00:00
-- url     : https://prove2.me/submissions/25eef893-6bf8-4945-aeb4-7fedf5c55ff5

import Definitions.Def_Submission_ThreeSum_LightFixedArithmetic
import Definitions.Def_Submission_ThreeSum_FiniteMomentZeroDetector
import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_sumCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_eval_prodCircuits
import Theorems.Thm_ThreeSum_LightMomentDeterminant_wordCoefficient_pos
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_bound_polynomial
import Theorems.Thm_ThreeSum_LightFixedArithmetic_Circuit_coefficient_pos
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
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero


attribute [local simp] ThreeSum.LightMomentDeterminant.eval_sumCircuits
attribute [local simp] ThreeSum.LightMomentDeterminant.eval_prodCircuits

set_option autoImplicit false
open ThreeSum ThreeSum.LightMomentDeterminant
open Light Matrix ThreeSum.LightFixedArithmetic
open scoped BigOperators
namespace ThreeSum.LightMomentDeterminant
theorem _root_.solution (h : ℕ) {U : ℤ} (hU : 0≤U) :
    wordBound U h≤wordCoefficient h*(U+1)^wordDegree h := by
  have hbase : 1≤U+1 := by omega
  induction h with
  | zero => simp [wordBound,wordCoefficient,wordDegree]
  | succ h ih =>
    have hco := wordCoefficient_pos h
    have hcl := (leading (h+1)).coefficient_pos
    have hcm := (modified (h+1)).coefficient_pos
    have hlo := (leading (h+1)).bound_polynomial hU
    have hmo := (modified (h+1)).bound_polynomial hU
    have hpold : (U+1)^wordDegree h≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hplead : (U+1)^(leading (h+1)).degree≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hpmod : (U+1)^(modified (h+1)).degree≤(U+1)^wordDegree (h+1) :=
      pow_le_pow_right₀ hbase (by simp only [wordDegree]; omega)
    have hpow : 0≤(U+1)^wordDegree (h+1) := le_trans (by decide : (0 : ℤ)≤1) (one_le_pow₀ hbase)
    change max (wordBound U h) (max ((leading (h+1)).bound U) ((modified (h+1)).bound U))≤_
    apply max_le
    · exact ih.trans ((mul_le_mul_of_nonneg_left hpold (by omega)).trans
        (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))
    · apply max_le
      · exact hlo.trans ((mul_le_mul_of_nonneg_left hplead (by omega)).trans
          (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))
      · exact hmo.trans ((mul_le_mul_of_nonneg_left hpmod (by omega)).trans
          (mul_le_mul_of_nonneg_right (by simp [wordCoefficient]; omega) hpow))
end ThreeSum.LightMomentDeterminant

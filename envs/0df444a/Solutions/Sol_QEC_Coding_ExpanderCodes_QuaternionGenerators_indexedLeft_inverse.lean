-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedLeft_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:57.36575+00:00
-- url     : https://prove2.me/submissions/7442fb91-3796-4210-b8ff-cc6dba4d59ce

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_alpha
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectiveAlpha_conjugate_base
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit


attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_mk

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F) (y : K)
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0) (hY : y ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) (t : TorusIndex epsilon) :
    indexedLeft f epsilon y hTwoF hY hOne hTwo (indexedLeftInverse epsilon hEpsilon t) =
      (indexedLeft f epsilon y hTwoF hY hOne hTwo t)⁻¹ := by
  change indexedLeft f epsilon y hTwoF hY hOne hTwo (t * torusIndexAlpha epsilon hEpsilon) = _
  simp only [indexedLeft, map_mul, torusIndexMap_alpha, mul_inv_rev]
  have hConjugate := projectiveAlpha_conjugate_base (f epsilon) y
    ((map_ne_zero f).mpr hEpsilon) hY hOne
  calc
    _ = torusIndexMap f epsilon y hTwoF hOne hTwo t *
        (projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) *
          projectiveBase (f epsilon) y hY hOne *
          (projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon))⁻¹) *
        (torusIndexMap f epsilon y hTwoF hOne hTwo t)⁻¹ := by simp only [mul_assoc]
    _ = _ := by rw [hConjugate]; simp only [mul_inv_rev, inv_inv, mul_assoc]
end QEC.Coding.ExpanderCodes.QuaternionGenerators

-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.indexedRight_inverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:17.283544+00:00
-- url     : https://prove2.me/submissions/077d9a55-6226-436c-a394-8681bc49481a

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_projectivePrime_sq
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
    indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t =
      (indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t)⁻¹ := by
  have hSquare : indexedRight f epsilon y hEpsilon hTwoF hY hOne hTwo t ^ 2 = 1 := by
    rw [indexedRight, conj_pow, projectivePrime_sq]
    simp
  exact (inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hSquare)).symm
end QEC.Coding.ExpanderCodes.QuaternionGenerators

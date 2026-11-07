-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexMap_alpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:35:14.609243+00:00
-- url     : https://prove2.me/submissions/e83eea94-8426-4075-bc17-e57e90907fc0

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
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
    (hEpsilon : epsilon ≠ 0) (hTwoF : (2 : F) ≠ 0)
    (hOne : 1 + y ≠ 0) (hTwo : (2 : K) ≠ 0) :
    torusIndexMap f epsilon y hTwoF hOne hTwo (torusIndexAlpha epsilon hEpsilon) =
      projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) := by
  rw [torusIndexAlpha, torusIndexMap_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Units.ext
  ext <;> simp [constantProjectiveMap, coefficientEmbedding, quadraticAlphaUnit, alpha]
end QEC.Coding.ExpanderCodes.QuaternionGenerators

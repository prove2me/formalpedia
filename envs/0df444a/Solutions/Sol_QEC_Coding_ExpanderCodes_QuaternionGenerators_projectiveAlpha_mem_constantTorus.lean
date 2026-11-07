-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.projectiveAlpha_mem_constantTorus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:34:37.812832+00:00
-- url     : https://prove2.me/submissions/fa266599-ae30-4477-8429-17fddda3a11b

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorus
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_alphaUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_baseUnit
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_val_primeUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_alphaUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_baseUnit
attribute [local simp] QEC.Coding.ExpanderCodes.QuaternionGenerators.val_primeUnit



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.QuaternionGenerators
open scoped QuadraticAlgebra
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K]
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
theorem _root_.solution (f : F →+* K) (epsilon : F)
    (y : K) (hEpsilon : epsilon ≠ 0) :
    projectiveAlpha (f epsilon) y ((map_ne_zero f).mpr hEpsilon) ∈
      constantTorus f epsilon y := by
  refine ⟨quadraticAlphaUnit epsilon hEpsilon, ?_⟩
  apply congrArg (QuotientGroup.mk' _)
  apply Units.ext
  ext <;> simp [quadraticAlphaUnit, coefficientEmbedding, alpha]
end QEC.Coding.ExpanderCodes.QuaternionGenerators

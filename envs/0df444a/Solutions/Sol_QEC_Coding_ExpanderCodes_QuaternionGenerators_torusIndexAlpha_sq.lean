-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndexAlpha_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:16.885334+00:00
-- url     : https://prove2.me/submissions/920b5675-117c-48d0-bfd1-c304c2a6e5a6

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
theorem _root_.solution (epsilon : F) (hEpsilon : epsilon ≠ 0)
    (hTwoF : (2 : F) ≠ 0) : torusIndexAlpha epsilon hEpsilon ^ 2 = 1 := by
  change (QuotientGroup.mk (quadraticAlphaUnit epsilon hEpsilon) : TorusIndex epsilon) ^ 2 = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  change constantProjectiveMap (RingHom.id F) epsilon 0
    (quadraticAlphaUnit epsilon hEpsilon ^ 2) = 1
  apply (constantProjectiveMap_eq_one_iff (RingHom.id F) epsilon 0 (by simp) hTwoF _).mpr
  simp [quadraticAlphaUnit, pow_two]
end QEC.Coding.ExpanderCodes.QuaternionGenerators

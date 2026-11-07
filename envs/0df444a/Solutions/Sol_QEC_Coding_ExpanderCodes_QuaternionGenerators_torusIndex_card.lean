-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.QuaternionGenerators.torusIndex_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:49:15.321188+00:00
-- url     : https://prove2.me/submissions/98896c2c-949d-4112-8d0f-4c08c5215cf5

import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticGeneratorSets
import Definitions.Def_QEC_Coding_ExpanderCodes_QuadraticTorusIndex
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_torusIndexMap_mk
import Theorems.Thm_QEC_Coding_ExpanderCodes_QuaternionGenerators_card_constantTorus
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
theorem _root_.solution (epsilon : F) [Fintype F]
    (hNonSquare : ∀ r : F, r ^ 2 ≠ epsilon) (hTwoF : (2 : F) ≠ 0) :
    Fintype.card (TorusIndex epsilon) = Fintype.card F + 1 := by
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr (torusIndexEquiv (RingHom.id F) epsilon 0 hTwoF (by simp) hTwoF).toEquiv]
  exact card_constantTorus (RingHom.id F) epsilon 0 hNonSquare (by simp) hTwoF
end QEC.Coding.ExpanderCodes.QuaternionGenerators

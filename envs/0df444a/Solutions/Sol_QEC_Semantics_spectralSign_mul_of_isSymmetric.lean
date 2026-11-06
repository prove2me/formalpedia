-- Prove2me | solution 1 for QEC.Semantics.spectralSign_mul_of_isSymmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:51:57.481698+00:00
-- url     : https://prove2.me/submissions/48343453-9b2b-4746-b758-597140306a8e

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_supportProjection_mul_positivePart
import Theorems.Thm_QEC_Semantics_supportProjection_mul_negativePart
import Theorems.Thm_QEC_Semantics_positiveSupportProjection_mul_negativePart
import Theorems.Thm_QEC_Semantics_negativeSupportProjection_mul_positivePart
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) (hA : A.IsSymmetric) :
    spectralSign A * LinearMap.toContinuousLinearMap A =
      (LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻ := by
  have hAclm : (LinearMap.toContinuousLinearMap A).IsSymmetric := hA
  calc
    spectralSign A * LinearMap.toContinuousLinearMap A =
        spectralSign A * ((LinearMap.toContinuousLinearMap A)⁺ -
          (LinearMap.toContinuousLinearMap A)⁻) := by
      rw [CFC.posPart_sub_negPart _ hAclm.isSelfAdjoint]
    _ = (LinearMap.toContinuousLinearMap A)⁺ +
        (LinearMap.toContinuousLinearMap A)⁻ := by
      simp only [spectralSign, sub_mul, mul_sub,
        supportProjection_mul_positivePart, supportProjection_mul_negativePart,
        positiveSupportProjection_mul_negativePart,
        negativeSupportProjection_mul_positivePart,
        sub_zero, zero_sub, sub_neg_eq_add]
end QEC.Semantics

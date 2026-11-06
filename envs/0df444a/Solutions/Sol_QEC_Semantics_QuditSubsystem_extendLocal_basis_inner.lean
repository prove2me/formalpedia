-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.extendLocal_basis_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:30:18.024349+00:00
-- url     : https://prove2.me/submissions/19ec4f6e-bf61-4d0f-81c1-704b9ad3209f

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators TensorProduct
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] {q : J → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q) (E : Operator S.selectedSystem)
    (x y : Qudit.Label q) :
    inner Complex (EuclideanSpace.basisFun (Qudit.Label q) Complex x)
      (S.extendLocalToRegister E (EuclideanSpace.basisFun (Qudit.Label q) Complex y)) =
    inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel x).1)
        (E (EuclideanSpace.basisFun (Qudit.Label S.selectedDimensions) Complex (S.splitLabel y).1)) *
      inner Complex
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel x).2)
        (EuclideanSpace.basisFun (Qudit.Label S.complementDimensions) Complex (S.splitLabel y).2) := by
  rw [← inner_conj_symm, extendLocalToRegister, UnitaryTransport.inner_conjOperator]
  simp only [UnitaryTransport.symm_toLinearEquiv, LinearEquiv.symm_symm]
  rw [S.registerFactorization_apply_basis, S.registerFactorization_apply_basis,
    S.extendLocal_apply_tmul, TensorProduct.inner_tmul]
  simp only [map_mul, inner_conj_symm]
end QEC.Semantics.QuditSubsystem

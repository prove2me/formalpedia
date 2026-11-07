-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.xorTransport_tensor_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:23:13.464028+00:00
-- url     : https://prove2.me/submissions/b7f06f3f-e76d-4c55-959f-ae18ab397563

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (a b : Fin 2) :
    xorTransport
        (tensorRegisterTransport
          (EuclideanSpace.basisFun (Fin 2) Complex a ⊗ₜ[Complex]
            EuclideanSpace.basisFun (Fin 2) Complex b)) =
      tensorRegisterTransport
        (EuclideanSpace.basisFun (Fin 2) Complex a ⊗ₜ[Complex]
          EuclideanSpace.basisFun (Fin 2) Complex
            (controlledXBit a b)) := by
  rw [tensorRegisterTransport_apply_basis]
  rw [xorTransport_apply_basis]
  rw [tensorRegisterTransport_apply_basis]
  simp [xorBitstring]
end QEC.Distillation.TwoQubit

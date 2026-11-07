-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.xorTransport_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:19:50.577441+00:00
-- url     : https://prove2.me/submissions/e6d4075c-c35c-4d94-af01-e9c34fb4b4fb

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    xorTransport (xorTransport psi) = psi := by
  let basis :=
    EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
  have h :
      xorTransport.toLinearEquiv.toLinearMap.comp
          xorTransport.toLinearEquiv.toLinearMap =
        LinearMap.id := by
    apply (Module.Basis.ext basis.toBasis)
    intro bits
    change
      xorTransport
          (xorTransport
            (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits)) =
        EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits
    rw [xorTransport_apply_basis]
    rw [xorTransport_apply_basis]
    rw [xorBitstring_involutive]
  exact LinearMap.congr_fun h psi
end QEC.Distillation.TwoQubit

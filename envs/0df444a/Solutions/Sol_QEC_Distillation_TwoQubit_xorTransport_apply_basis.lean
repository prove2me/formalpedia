-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.xorTransport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:18:33.585049+00:00
-- url     : https://prove2.me/submissions/72e6b04e-933f-4727-b945-ee4609cf2c49

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (bits : Bitstring (Fin 2)) :
    xorTransport
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex
        (xorBitstring bits) := by
  dsimp [xorTransport]
  rw [OrthonormalBasis.equiv_apply_basis]
  rfl
end QEC.Distillation.TwoQubit

-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.xorTransport_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:21:34.662193+00:00
-- url     : https://prove2.me/submissions/740f0af0-e2ee-4add-afa3-048c86b28286

import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
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

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
open scoped TensorProduct
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    xorTransport.symm psi = xorTransport psi := by
  apply xorTransport.toLinearEquiv.injective
  simp only [UnitaryTransport.symm]
  rw [xorTransport.toLinearEquiv.apply_symm_apply]
  exact (xorTransport_involutive psi).symm
end QEC.Distillation.TwoQubit

-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddProjector_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:59:50.769111+00:00
-- url     : https://prove2.me/submissions/f6a6cbf8-8088-4ede-87d5-e4c2866f9826

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_adjoint
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_apply_basis
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_involutive
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_symm_apply
attribute [local simp] QEC.Distillation.TwoQubit.xorTransport_tensor_basis
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator


attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply
attribute [local simp] QEC.Distillation.TwoQubit.zzOperator_apply_basis

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
namespace QEC.Distillation.TwoQubit
theorem _root_.solution :
    LinearMap.adjoint zzOddProjector = zzOddProjector := by
  apply LinearMap.IsSymmetric.adjoint_eq
  unfold zzOddProjector
  apply LinearMap.IsSymmetric.smul
  · simp only [starRingEnd_apply, star_inv₀, star_ofNat]
  · apply LinearMap.IsSymmetric.sub
    · exact LinearMap.IsSymmetric.one
    · rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
      exact zzOperator_adjoint
end QEC.Distillation.TwoQubit

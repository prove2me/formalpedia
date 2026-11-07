-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOperator_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:51.887716+00:00
-- url     : https://prove2.me/submissions/b884bece-2743-4162-b761-75ab5845b5c9

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOperator_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_apply_basis
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_involutive
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_symm_apply
import Theorems.Thm_QEC_Distillation_TwoQubit_xorTransport_tensor_basis
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZ_localZ_commute
import Theorems.Thm_QEC_Semantics_Qubit_localZ_square
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
    zzOperator * zzOperator = (1 : Operator TwoQubitSpace) := by
  unfold zzOperator
  calc
    (localZ (0 : Fin 2) * localZ (1 : Fin 2)) *
          (localZ (0 : Fin 2) * localZ (1 : Fin 2)) =
        (localZ (0 : Fin 2) *
            (localZ (1 : Fin 2) * localZ (0 : Fin 2))) *
          localZ (1 : Fin 2) := by
      simp only [mul_assoc]
    _ = (localZ (0 : Fin 2) *
          (localZ (0 : Fin 2) * localZ (1 : Fin 2))) *
        localZ (1 : Fin 2) := by
      rw [localZ_localZ_commute (1 : Fin 2) (0 : Fin 2)]
    _ = (localZ (0 : Fin 2) * localZ (0 : Fin 2)) *
        (localZ (1 : Fin 2) * localZ (1 : Fin 2)) := by
      simp only [mul_assoc]
    _ = 1 := by
      rw [localZ_square, localZ_square, one_mul]
end QEC.Distillation.TwoQubit

-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenProjector_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:29:50.921826+00:00
-- url     : https://prove2.me/submissions/bc8ccb98-e2d3-4016-8036-7925062f8245

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
theorem _root_.solution (bits : Bitstring (Fin 2)) :
    zzEvenProjector
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits) =
      if bits 0 = bits 1 then
        EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits
      else 0 := by
  change
    (2 : Complex)⁻¹ •
        (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits +
          zzOperator
            (EuclideanSpace.basisFun (Bitstring (Fin 2)) Complex bits)) =
      _
  rw [zzOperator_apply_basis]
  by_cases h : bits 0 = bits 1
  · simp only [if_pos h]
    rw [h, zPhase_sq]
    module
  · simp only [if_neg h]
    have hphase :
        zPhase (bits 0) * zPhase (bits 1) = (-1 : Complex) := by
      generalize hfirst : bits 0 = firstBit at *
      generalize hsecond : bits 1 = secondBit at *
      fin_cases firstBit <;> fin_cases secondBit <;> simp_all [zPhase]
    rw [hphase]
    module
end QEC.Distillation.TwoQubit

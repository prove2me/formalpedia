-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.cssXCheck_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:35.457489+00:00
-- url     : https://prove2.me/submissions/bf239cbd-0b90-4eb3-9f94-1240b63d31db

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Theorems.Thm_QEC_Coding_PauliSymplectic_flipSupport_binarySupport_eq_add
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PauliSymplectic
open Semantics
universe u
variable {J : Type u} [Fintype J] [DecidableEq J]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (x y : Word (ZMod 2) J) :
    toQubitOperator (cssXCheck x) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      EuclideanSpace.basisFun (Word (ZMod 2) J) Complex (y + x) := by
  classical
  ext z
  let w : Word (ZMod 2) J := z
  have hxx : x + x = 0 := by
    ext j
    change x j + x j = (0 : ZMod 2)
    generalize x j = b
    fin_cases b <;> rfl
  have hiff : w + x = y ↔ w = y + x := by
    constructor
    · intro h
      rw [← h, add_assoc, hxx, add_zero]
    · intro h
      rw [h, add_assoc, hxx, add_zero]
  erw [toQubitOperator_apply]
  simp [cssXCheck, xSupport, zSupport,
    Qubit.zSupportPhase, flipSupport_binarySupport_eq_add,
    EuclideanSpace.basisFun_apply, binaryPhaseScalar_zero, one_mul,
    Pi.single_apply]
  change Pi.single (M := fun _ : Word (ZMod 2) J => Complex)
      y (1 : Complex) (Qubit.flipSupport (binarySupport x) w) =
    Pi.single (M := fun _ : Word (ZMod 2) J => Complex) (y + x) (1 : Complex) w
  erw [flipSupport_binarySupport_eq_add]
  simp only [Pi.single_apply, hiff]
end QEC.Coding.PauliSymplectic

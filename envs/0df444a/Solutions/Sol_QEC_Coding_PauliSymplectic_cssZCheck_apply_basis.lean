-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.cssZCheck_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:37:56.203175+00:00
-- url     : https://prove2.me/submissions/d5a594e9-6680-4671-86aa-01846dc664dd

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_BasisAction
import Theorems.Thm_QEC_Coding_PauliSymplectic_bitstringWordEquiv_eq_self
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
theorem _root_.solution (z y : Word (ZMod 2) J) :
    toQubitOperator (cssZCheck z) (EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y) =
      binaryPhaseScalar (wordPairing z y) •
        EuclideanSpace.basisFun (Word (ZMod 2) J) Complex y := by
  classical
  have hphase := zSupportPhase_eq_binaryPhaseScalar_wordPairing z y
  rw [bitstringWordEquiv_eq_self] at hphase
  ext bits
  let w : Word (ZMod 2) J := bits
  erw [toQubitOperator_apply]
  simp only [cssZCheck, xSupport, zSupport, binaryPhaseScalar_zero, one_mul,
    EuclideanSpace.basisFun_apply, PiLp.smul_apply]
  change Qubit.zSupportPhase (binarySupport z) (Qubit.flipSupport (binarySupport 0) w) *
    Pi.single (M := fun _ : Word (ZMod 2) J => Complex)
      y (1 : Complex) (Qubit.flipSupport (binarySupport 0) w) =
    (binaryPhaseScalar (wordPairing z y) •
      Pi.single (M := fun _ : Word (ZMod 2) J => Complex) y (1 : Complex)) w
  erw [show binarySupport (0 : Word (ZMod 2) J) = ∅ by simp [binarySupport]]
  erw [Qubit.flipSupport_empty]
  by_cases hw : y = w
  · erw [← hw]
    simp [cssZCheck, xSupport, zSupport, EuclideanSpace.basisFun_apply]
    exact hphase
  · simp [toQubitOperator_apply, cssZCheck, xSupport, zSupport,
      EuclideanSpace.basisFun_apply, hw]
end QEC.Coding.PauliSymplectic

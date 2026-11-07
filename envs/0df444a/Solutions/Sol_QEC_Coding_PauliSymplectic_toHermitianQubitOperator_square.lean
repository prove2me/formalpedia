-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toHermitianQubitOperator_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:25:07.043069+00:00
-- url     : https://prove2.me/submissions/419a22a7-9633-41d4-93e9-70f74eacc393

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_neg_one_pow_binaryOverlapCount
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toQubitOperator_eq_binaryDagger
import Theorems.Thm_QEC_Coding_PauliSymplectic_binaryPhaseScalar_binaryDaggerPhase
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_adjoint_comp_self
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


attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
section
noncomputable section
namespace QEC
namespace Coding
namespace PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
private theorem hermitianPhaseScalar_mul_self (P : Binary ι) :
    hermitianPhaseScalar P * hermitianPhaseScalar P =
      binarySwapPhase P.vector.xPart P.vector.zPart := by
  calc
    hermitianPhaseScalar P * hermitianPhaseScalar P =
        Complex.I ^ binaryOverlapCount P *
          Complex.I ^ binaryOverlapCount P := rfl
    _ = (Complex.I * Complex.I) ^ binaryOverlapCount P := by
          rw [mul_pow]
    _ = (-1 : Complex) ^ binaryOverlapCount P := by
          rw [Complex.I_mul_I]
    _ = binarySwapPhase P.vector.xPart P.vector.zPart :=
          (binarySwapPhase_eq_neg_one_pow_binaryOverlapCount P).symm
private theorem adjoint_toQubitOperator_eq_binarySwapPhase_smul
    (P : Binary ι) :
    LinearMap.adjoint (toQubitOperator P) =
      binarySwapPhase P.vector.xPart P.vector.zPart •
        toQubitOperator P := by
  rw [adjoint_toQubitOperator_eq_binaryDagger]
  unfold toQubitOperator
  simp only [binaryDagger, xSupport, zSupport]
  rw [binaryPhaseScalar_binaryDaggerPhase]
  simp only [smul_smul]
  congr 1
  exact mul_comm _ _
end PauliSymplectic
end Coding
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Classical
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P : Binary ι) :
    toHermitianQubitOperator P * toHermitianQubitOperator P = 1 := by
  calc
    toHermitianQubitOperator P * toHermitianQubitOperator P =
        (hermitianPhaseScalar P * hermitianPhaseScalar P) •
          (toQubitOperator P * toQubitOperator P) := by
            exact smul_mul_smul_comm _ _ _ _
    _ = binarySwapPhase P.vector.xPart P.vector.zPart •
        (toQubitOperator P * toQubitOperator P) := by
          rw [hermitianPhaseScalar_mul_self]
    _ = (binarySwapPhase P.vector.xPart P.vector.zPart •
          toQubitOperator P) * toQubitOperator P := by
          rw [smul_mul_assoc]
    _ = LinearMap.adjoint (toQubitOperator P) * toQubitOperator P := by
          rw [adjoint_toQubitOperator_eq_binarySwapPhase_smul]
    _ = 1 := by
          simpa [Module.End.mul_eq_comp] using
            toQubitOperator_adjoint_comp_self P
end QEC.Coding.PauliSymplectic

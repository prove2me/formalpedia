-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binarySign_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:40:29.107124+00:00
-- url     : https://prove2.me/submissions/e64dbdd5-a235-46d7-b163-d26202e8c98b

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_binaryMul
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
private theorem binaryOverlapCount_binarySign_mul
    (phase : ZMod 2) (P : Binary ι) :
    binaryOverlapCount (binaryMul (binarySign phase) P) =
      binaryOverlapCount P := by
  apply congrArg Finset.card
  ext i
  simp [binaryOverlapSupport, xSupport, zSupport, binarySupport, binaryMul,
    binarySign]
private theorem toQubitOperator_binarySign (phase : ZMod 2) :
    toQubitOperator (binarySign (ι := ι) phase) =
      binaryPhaseScalar phase •
        (1 : Semantics.Operator (Semantics.Qubit.QubitRegister ι)) := by
  simp [toQubitOperator, binarySign, xSupport, zSupport, binarySupport]
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
theorem _root_.solution
    (phase : ZMod 2) (P : Binary ι) :
    toHermitianQubitOperator (binaryMul (binarySign phase) P) =
      binaryPhaseScalar phase • toHermitianQubitOperator P := by
  unfold toHermitianQubitOperator hermitianPhaseScalar
  rw [binaryOverlapCount_binarySign_mul, toQubitOperator_binaryMul,
    toQubitOperator_binarySign]
  simp only [smul_mul_assoc, one_mul, smul_smul]
  rw [mul_comm]
end QEC.Coding.PauliSymplectic

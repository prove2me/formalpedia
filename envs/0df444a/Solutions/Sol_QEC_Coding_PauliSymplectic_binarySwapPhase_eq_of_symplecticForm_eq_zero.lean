-- Prove2me | solution 1 for QEC.Coding.PauliSymplectic.binarySwapPhase_eq_of_symplecticForm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:35.364027+00:00
-- url     : https://prove2.me/submissions/f43761bd-658a-430e-b70c-d5e41ead79a6

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Coding_PauliSymplectic_binarySwapPhase_eq_binaryPhaseScalar_sum_mul
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
open QEC
open QEC.Coding
open Classical
open scoped BigOperators
universe u w
open QEC.Coding.PauliSymplectic
variable {ι : Type u} [Fintype ι]
variable [DecidableEq ι]
namespace QEC.Coding.PauliSymplectic
theorem _root_.solution (P Q : Binary ι)
    (h : symplecticForm P.vector Q.vector = 0) :
    binarySwapPhase Q.vector.xPart P.vector.zPart =
      binarySwapPhase P.vector.xPart Q.vector.zPart := by
  rw [binarySwapPhase_eq_binaryPhaseScalar_sum_mul,
    binarySwapPhase_eq_binaryPhaseScalar_sum_mul]
  apply congrArg binaryPhaseScalar
  have hdot :
      Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) =
        Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) := by
    have hsub :
        Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) -
            Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) = 0 := by
      simpa [symplecticForm, Finset.sum_sub_distrib] using h
    exact sub_eq_zero.mp hsub
  calc
    Finset.sum Finset.univ (fun i => Q.vector.xPart i * P.vector.zPart i)
        = Finset.sum Finset.univ (fun i => P.vector.zPart i * Q.vector.xPart i) := by
          simp [mul_comm]
    _ = Finset.sum Finset.univ (fun i => P.vector.xPart i * Q.vector.zPart i) := hdot.symm
end QEC.Coding.PauliSymplectic

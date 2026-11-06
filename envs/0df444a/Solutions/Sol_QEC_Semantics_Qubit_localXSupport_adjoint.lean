-- Prove2me | solution 1 for QEC.Semantics.Qubit.localXSupport_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:27:49.907647+00:00
-- url     : https://prove2.me/submissions/adc933e9-6b37-4dfa-9966-614326e1f85d

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_commute
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_insert
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_singleton
import Theorems.Thm_QEC_Semantics_Qubit_localX_adjoint
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
open QEC.Semantics
open QEC.Semantics.Qubit
open Classical
open scoped BigOperators
universe u
variable {ι : Type u}
variable [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.Qubit
theorem _root_.solution (s : Finset ι) :
    LinearMap.adjoint (localXSupport s) = localXSupport s := by
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro i s his hs
    calc
      LinearMap.adjoint (localXSupport (insert i s))
          = LinearMap.adjoint (localX i * localXSupport s) := by
              rw [localXSupport_insert s his]
      _ = LinearMap.adjoint (localXSupport s) * LinearMap.adjoint (localX i) := by
              simp [Module.End.mul_eq_comp]
      _ = localXSupport s * localX i := by
              rw [hs, localX_adjoint]
      _ = localX i * localXSupport s := by
              simpa [localXSupport_singleton] using
                (localXSupport_commute s ({i} : Finset ι))
      _ = localXSupport (insert i s) := by
              rw [localXSupport_insert s his]
end QEC.Semantics.Qubit

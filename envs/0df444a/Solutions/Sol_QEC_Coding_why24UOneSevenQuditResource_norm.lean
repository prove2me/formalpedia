-- Prove2me | solution 1 for QEC.Coding.why24UOneSevenQuditResource_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:11:55.7502+00:00
-- url     : https://prove2.me/submissions/4d46e9ae-9cb0-4b99-8a28-656ec2fc9702

import Definitions.Def_QEC_Coding_QuditQubitConversion_AppendixANF_Gate_ReversePhase
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Coding_QuditQubitConversion_ResourceCircuit
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_Why24BooleanANF_evaluate_generator
import Theorems.Thm_QEC_Coding_Why24BooleanANF_generator_mul_self
import Theorems.Thm_QEC_Coding_why24QuditZ_apply
import Theorems.Thm_QEC_Coding_why24U_apply
import Theorems.Thm_QEC_Coding_why24U_isUnitary
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.Why24BooleanANF.evaluate_generator
attribute [local simp] QEC.Coding.Why24BooleanANF.generator_mul_self
attribute [local simp] QEC.Coding.why24QuditZ_apply
attribute [local simp] QEC.Coding.why24U_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.Qubit.localXSupport_apply
attribute [local simp] QEC.Semantics.Qubit.localZSupport_apply
attribute [local simp] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator


section
noncomputable section
namespace QEC.Coding
private theorem why24QuditPlusState_inner_self :
    inner Complex why24QuditPlusState why24QuditPlusState = 1 := by
  rw [PiLp.inner_apply]
  simp only [why24QuditPlusState_apply, RCLike.inner_apply]
  rw [Finset.sum_const, nsmul_eq_mul]
  change (Fintype.card F1024 : Complex) *
      (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) = 1
  calc
    (Fintype.card F1024 : Complex) *
        (why24UniformAmplitude * starRingEnd Complex why24UniformAmplitude) =
        starRingEnd Complex why24UniformAmplitude * why24UniformAmplitude *
          (Fintype.card F1024 : Complex) := by ring
    _ = 1 := why24UniformAmplitude_identity
end QEC.Coding
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
namespace QEC.Coding
theorem _root_.solution : ‖why24UOneSevenQuditResource‖ = 1 := by
  have hinner := why24U_isUnitary (1 : F1024) 7
    why24QuditPlusState why24QuditPlusState
  change inner Complex why24UOneSevenQuditResource why24UOneSevenQuditResource =
    inner Complex why24QuditPlusState why24QuditPlusState at hinner
  rw [why24QuditPlusState_inner_self] at hinner
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hsquare : ‖why24UOneSevenQuditResource‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact hinner
  nlinarith [norm_nonneg why24UOneSevenQuditResource]
end QEC.Coding

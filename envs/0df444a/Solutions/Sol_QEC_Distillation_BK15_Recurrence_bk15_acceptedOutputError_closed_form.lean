-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15_acceptedOutputError_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:27:22.905644+00:00
-- url     : https://prove2.me/submissions/94b7f78a-14c6-402e-88b6-312a8ae02a28

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_recurrence_denominator_pos
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_endpointWeight_eq_closedForm
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_negativeA_weight_eq_closedForm
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
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
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerConditionalDensity_toOperator
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_kraus
attribute [local simp] QEC.Coding.PauliSymplectic.stabilizerInstrument_observe
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_apply
attribute [local simp] QEC.Coding.PauliSymplectic.toHermitianQubitOperator_binaryOne
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_acceptedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_operation
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_rejectedOutput
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_resourceCount
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hResourceTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.sourceHDensity_toOperator
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
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
namespace QEC
namespace Distillation
namespace BK15
namespace Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
private theorem aInputError_eq_negativeA_trace
    (rho : DensityOperator QubitSpace) :
    aInputError rho =
      (LinearMap.trace Complex QubitSpace
        (aBasisProjector .negative * rho.toOperator)).re := by
  have hsum : aInputSquaredOverlap rho +
      OneQubitMagic.projectionSquaredOverlap
        (aBasisProjector .negative) rho = 1 := by
    unfold aInputSquaredOverlap OneQubitMagic.projectionSquaredOverlap
    have htrace :
        LinearMap.trace Complex QubitSpace
            (aBasisProjector .positive * rho.toOperator) +
          LinearMap.trace Complex QubitSpace
            (aBasisProjector .negative * rho.toOperator) = 1 := by
      calc
        LinearMap.trace Complex QubitSpace
            (aBasisProjector .positive * rho.toOperator) +
          LinearMap.trace Complex QubitSpace
            (aBasisProjector .negative * rho.toOperator) =
            LinearMap.trace Complex QubitSpace
              ((aBasisProjector .positive + aBasisProjector .negative) *
                rho.toOperator) := by
              rw [add_mul, map_add]
        _ = LinearMap.trace Complex QubitSpace rho.toOperator := by
              rw [aBasisProjector_add, one_mul]
        _ = 1 := rho.trace_one
    have hre := congrArg Complex.re htrace
    exact_mod_cast hre
  unfold aInputError
  have hnegative :
      OneQubitMagic.projectionSquaredOverlap
          (aBasisProjector .negative) rho =
        1 - aInputSquaredOverlap rho := by
    linarith
  rw [← hnegative]
  rfl
private theorem qubitEndpointConditional_accepted_toOperator
    (epsilon : BK15Epsilon)
    (hpositive : 0 < endpointWeight epsilon .accepted) :
    (qubitEndpointConditional epsilon .accepted hpositive).toOperator =
      ((endpointWeight epsilon .accepted : Complex)⁻¹) •
        decoderToQubitChannel (rawEndpoint epsilon .accepted) := by
  have hdecode (rho : DensityOperator BK15Register) :
      (logicalRegisterToQubit.conjDensity (decoderChannel.mapDensity rho)).toOperator =
        decoderToQubitChannel rho.toOperator := by
    rw [UnitaryTransport.conjDensity_toOperator,
      QuantumChannel.mapDensity_toOperator]
    rfl
  change (logicalRegisterToQubit.conjDensity
    (decoderChannel.mapDensity (endpointConditional epsilon .accepted hpositive))).toOperator = _
  rw [hdecode, endpointConditional_toOperator]
  exact decoderToQubitChannel.toLinearMap.map_smul _ _
private theorem acceptedOutput_error_eq_raw_normalization
    (epsilon : BK15Epsilon)
    (hpositive : 0 < endpointWeight epsilon .accepted) :
    aInputError (qubitEndpointConditional epsilon .accepted hpositive) =
      acceptedNegativeAWeight epsilon / endpointWeight epsilon .accepted := by
  rw [aInputError_eq_negativeA_trace,
    qubitEndpointConditional_accepted_toOperator]
  unfold acceptedNegativeAWeight negativeADecodedTrace
  rw [mul_smul_comm, map_smul]
  have hscalar :
      ((endpointWeight epsilon .accepted : Complex)⁻¹) =
        ((endpointWeight epsilon .accepted)⁻¹ : Real) := by
    norm_cast
  rw [hscalar]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  simp only [zero_mul, sub_zero, div_eq_mul_inv]
  change (endpointWeight epsilon .accepted)⁻¹ *
      (LinearMap.trace Complex QubitSpace
        (aBasisProjector .negative *
          decoderToQubitChannel (rawEndpoint epsilon .accepted))).re =
    (LinearMap.trace Complex QubitSpace
      (aBasisProjector .negative *
        decoderToQubitChannel (rawEndpoint epsilon .accepted))).re *
      (endpointWeight epsilon .accepted)⁻¹
  ring
end Recurrence
end BK15
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / (2 * (1 + 15 * bk15_r epsilon ^ 8)) := by
  rw [bk15Run_acceptedOutput, bk15OutputError,
    acceptedOutput_error_eq_raw_normalization,
    accepted_negativeA_weight_eq_closedForm,
    accepted_endpointWeight_eq_closedForm]
  have hdenom : 1 + 15 * bk15_r epsilon ^ 8 ≠ 0 :=
    (bk15_recurrence_denominator_pos epsilon).ne'
  field_simp [hdenom]
  ring
end QEC.Distillation.BK15.Recurrence

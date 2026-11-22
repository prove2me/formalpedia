-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15HfidelityDistillation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:48:20.570612+00:00
-- url     : https://prove2.me/submissions/020fee29-d5fa-4f6f-93b9-05106d283e38

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_zero
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_antitone
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_eventually_lt
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15IterationEpsilon_error
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInputError_nonneg
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInputError_lt_epsilonStar_of_FStar_lt
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInput_dephased_eq_diagonalAResource
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_leafCount
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15SemanticSchedule_realizesRun
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15HInput_actualAccepted_error
import Theorems.Thm_QEC_Distillation_BK15_Threshold_sourceAReturnedHInfidelity_le_aInputError
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedLayerHInfidelity_le_iteration_succ
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15AcceptedRunHOutput_succ_eq_semanticSchedule
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
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_zeroEpsilon_decoded_output_error
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hFidelity_mem_Icc
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


attribute [local simp] QEC.Distillation.BK15.Threshold.bk15Iteration_zero
attribute [local simp] QEC.Distillation.BK15.Threshold.bk15IterationEpsilon_error
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace BK15SemanticSchedule
end BK15SemanticSchedule
private theorem bk15IdealReturnedHOutput_infidelity_zero :
    1 - hFidelity bk15IdealReturnedHOutput ^ 2 = 0 := by
  have hbound := sourceAReturnedHInfidelity_le_aInputError
    (decodedOperation.mapDensity (rawInput zeroEpsilon))
  have hsource_zero :
      aInputError (decodedOperation.mapDensity (rawInput zeroEpsilon)) = 0 := by
    simpa [bk15OutputError] using zeroEpsilon_decoded_output_error
  have hle : 1 - hFidelity bk15IdealReturnedHOutput ^ 2 <= 0 := by
    simpa [bk15IdealReturnedHOutput, hsource_zero] using hbound
  have hfidelity := hFidelity_mem_Icc bk15IdealReturnedHOutput
  have hfactor : 0 <= hFidelity bk15IdealReturnedHOutput *
      (1 - hFidelity bk15IdealReturnedHOutput) :=
    mul_nonneg hfidelity.1 (sub_nonneg.mpr hfidelity.2)
  nlinarith
private theorem bk15AcceptedRunHInfidelity_succ_le_iteration
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar) (rounds : Nat) :
    bk15AcceptedRunHInfidelity rho (rounds + 1) <=
      bk15Iteration (bk15HInputError rho) (rounds + 1) := by
  rw [bk15AcceptedRunHInfidelity, bk15AcceptedRunHOutput_succ_eq_semanticSchedule
    rho hpositive hthreshold]
  rw [bk15SemanticSchedule_rootOutput_eq_bk15Run_acceptedOutput
    rho hpositive hthreshold rounds]
  exact bk15AcceptedLayerHInfidelity_le_iteration_succ
    (bk15HInputError rho) hpositive hthreshold rounds
private theorem bk15AcceptedRunHInfidelity_ideal
    (rho : DensityOperator QubitSpace)
    (hzero : bk15HInputError rho = 0) (rounds : Nat) :
    bk15AcceptedRunHInfidelity rho rounds = 0 := by
  have hnot_strict : ¬ (0 < bk15HInputError rho ∧
      bk15HInputError rho < epsilonStar) := by
    rintro ⟨hpositive, _⟩
    linarith
  unfold bk15AcceptedRunHInfidelity
  rw [bk15AcceptedRunHOutput, dif_neg hnot_strict]
  rw [if_pos hzero]
  exact bk15IdealReturnedHOutput_infidelity_zero
private theorem bk15HfidelityDistillation_strict
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hthreshold : bk15HInputError rho < epsilonStar)
    (delta : Real) (hdelta : 0 < delta) :
    hCanonicalizedDephasedInput rho =
        diagonalAResource
          (bk15HInputEpsilon rho hpositive
            (hthreshold.trans epsilonStar_lt_half).le) ∧
      bk15Recurrence (bk15HInputError rho) =
        bk15OutputError
          (bk15Run
            (bk15HInputEpsilon rho hpositive
              (hthreshold.trans epsilonStar_lt_half).le)
            (bk15HInputEpsilon_pos rho hpositive
            (hthreshold.trans epsilonStar_lt_half).le)).acceptedOutput
          aZeroDensity ∧
      ∃ depth : Nat,
        bk15AcceptedRunHInfidelity rho (depth + 1) < delta ∧
        BK15SemanticSchedule.leafCount
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          15 ^ (depth + 1) ∧
        BK15SemanticSchedule.rootInput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
        BK15SemanticSchedule.preparedInput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
            ((bk15Run
              (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
              (bk15Iteration_pos_and_lt_epsilonStar
                (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
        BK15SemanticSchedule.rootOutput
            (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
          (bk15Run
            (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
            (bk15Iteration_pos_and_lt_epsilonStar
              (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
        bk15AcceptedRunHOutput rho (depth + 1) =
          sourceA0Transport.symm.conjDensity
            (BK15SemanticSchedule.rootOutput
              (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1))) := by
  have hhalf : bk15HInputError rho <= 1 / 2 :=
    (hthreshold.trans epsilonStar_lt_half).le
  refine ⟨bk15HInput_dephased_eq_diagonalAResource rho hpositive hhalf,
    bk15HInput_actualAccepted_error rho hpositive hhalf, ?_⟩
  rcases bk15Iteration_eventually_lt (bk15HInputError rho) delta
      hpositive hthreshold hdelta with ⟨depth, hdepth⟩
  have hrealization :=
    bk15SemanticSchedule_realizesRun rho hpositive hthreshold depth
  refine ⟨depth, ?_, bk15SemanticSchedule_leafCount rho hpositive hthreshold
    (depth + 1), hrealization.2.1, hrealization.2.2.1,
    hrealization.2.2.2, ?_⟩
  · calc
      bk15AcceptedRunHInfidelity rho (depth + 1) <=
          bk15Iteration (bk15HInputError rho) (depth + 1) :=
        bk15AcceptedRunHInfidelity_succ_le_iteration rho hpositive hthreshold depth
      _ <= bk15Iteration (bk15HInputError rho) depth :=
        bk15Iteration_antitone (bk15HInputError rho) hpositive hthreshold
          (Nat.le_succ depth)
      _ < delta := hdepth
  · exact bk15AcceptedRunHOutput_succ_eq_semanticSchedule
      rho hpositive hthreshold depth
end Threshold
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
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution
    (rho : DensityOperator QubitSpace)
    (hfidelity : FStar < hFidelity rho) (delta : Real) (hdelta : 0 < delta) :
    ∃ rounds : Nat,
      bk15AcceptedRunHInfidelity rho rounds < delta ∧
        (bk15HInputError rho = 0 ∨
          ∃ (hpositive : 0 < bk15HInputError rho)
            (hthreshold : bk15HInputError rho < epsilonStar) (depth : Nat),
            rounds = depth + 1 ∧
            BK15SemanticSchedule.leafCount
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              15 ^ (depth + 1) ∧
            BK15SemanticSchedule.rootInput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput ∧
            BK15SemanticSchedule.preparedInput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).prepareInput
                ((bk15Run
                  (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                  (bk15Iteration_pos_and_lt_epsilonStar
                    (bk15HInputError rho) hpositive hthreshold depth).1).noisyInput) ∧
            BK15SemanticSchedule.rootOutput
                (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)) =
              (bk15Run
                (bk15IterationEpsilon (bk15HInputError rho) hpositive hthreshold depth)
                (bk15Iteration_pos_and_lt_epsilonStar
                  (bk15HInputError rho) hpositive hthreshold depth).1).acceptedOutput ∧
            bk15AcceptedRunHOutput rho (depth + 1) =
              sourceA0Transport.symm.conjDensity
                (BK15SemanticSchedule.rootOutput
                  (bk15CompleteSemanticSchedule rho hpositive hthreshold (depth + 1)))) := by
  have hthreshold : bk15HInputError rho < epsilonStar :=
    bk15HInputError_lt_epsilonStar_of_FStar_lt rho hfidelity
  by_cases hzero : bk15HInputError rho = 0
  · refine ⟨0, ?_, Or.inl hzero⟩
    rw [bk15AcceptedRunHInfidelity_ideal rho hzero]
    exact hdelta
  · have hpositive : 0 < bk15HInputError rho :=
      lt_of_le_of_ne (bk15HInputError_nonneg rho) (Ne.symm hzero)
    rcases bk15HfidelityDistillation_strict rho hpositive hthreshold delta hdelta with
      ⟨_, _, depth, hinfidelity, hleafCount, hinput, hprepared, houtput, hreturned⟩
    exact ⟨depth + 1, hinfidelity,
      Or.inr ⟨hpositive, hthreshold, depth, rfl, hleafCount, hinput, hprepared,
        houtput, hreturned⟩⟩
end QEC.Distillation.BK15.Threshold

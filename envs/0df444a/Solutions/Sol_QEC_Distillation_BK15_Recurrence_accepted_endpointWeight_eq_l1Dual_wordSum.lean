-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.accepted_endpointWeight_eq_l1Dual_wordSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:51:46.403626+00:00
-- url     : https://prove2.me/submissions/0f6f4f68-2466-4506-b2fa-3aea0afcc17f

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_adjoint_toHermitianQubitOperator_eq_self
import Theorems.Thm_QEC_Coding_PauliSymplectic_cssXCheck_toQubitOperator_commute_cssZCheck_of_wordPairing_eq_zero
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_eigen
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_square
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_anticommute_of_not_commutes
import Theorems.Thm_QEC_Coding_PauliSymplectic_toQubitOperator_commute_of_commutes
import Theorems.Thm_QEC_Coding_symplecticForm_x_zero_zero_z_eq_wordPairing
import Theorems.Thm_QEC_Distillation_BK15_Protocol_aWordCorrectionTransport_eigen
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_acceptedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_operation
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_rejectedOutput
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_resourceCount
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
import Theorems.Thm_QEC_Distillation_BK15_l1CoefficientMap_eq_sum
import Theorems.Thm_QEC_Distillation_BK15_l1_dimension
import Theorems.Thm_QEC_Distillation_BK15_l1_dual_carrier_eq_l1Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_l2_dual_carrier_eq_l2Syndrome_ker
import Theorems.Thm_QEC_Distillation_BK15_mem_l1DualWords_iff
import Theorems.Thm_QEC_Distillation_BK15_mem_l2_dual_iff_exists_l1_plus_allOnes
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hResourceTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceHDensity_toOperator
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_mem
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encoding_apply_of_not_mem
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
import Definitions.Def_QEC_Distillation_BK15_EndpointPart5_QECert
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
private theorem historyOutcome_accepted_iff
    (zOutcome : ZJointSyndrome) (xOutcome : XJointSyndrome) :
    historyOutcome (zOutcome, xOutcome) = .accepted ↔
      xOutcome = signSyndrome (0 : XCheckIndex → Bit) := by
  constructor
  · intro haccepted
    change (if binarySyndrome xOutcome = 0 then DistillationOutcome.accepted
      else DistillationOutcome.rejected) = DistillationOutcome.accepted at haccepted
    by_cases hzero : binarySyndrome xOutcome = 0
    ·
      calc
        xOutcome = signSyndrome (binarySyndrome xOutcome) :=
          (signSyndrome_binarySyndrome xOutcome).symm
        _ = signSyndrome 0 := by rw [hzero]
    · simp [hzero] at haccepted
  · intro hzero
    subst xOutcome
    simp [historyOutcome, binarySyndrome_signSyndrome]
set_option maxRecDepth 262144 in
private theorem accepted_history_word_sum (weight : Word → Real) :
    ∑ history : History,
      (if historyOutcome history = .accepted then
        ∑ word : Word, weight word *
          ‖historyKraus history (bk15ErrorWordState word)‖ ^ 2
      else 0) =
      ∑ word : Word, weight word *
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState word)‖ ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  calc
    ∑ zOutcome : ZJointSyndrome, ∑ xOutcome : XJointSyndrome,
        (if historyOutcome (zOutcome, xOutcome) = .accepted then
          ∑ word : Word, weight word *
            ‖historyKraus (zOutcome, xOutcome)
              (bk15ErrorWordState word)‖ ^ 2
        else 0) =
      ∑ zOutcome : ZJointSyndrome, ∑ word : Word, weight word *
        ‖historyKraus
          (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
          (bk15ErrorWordState word)‖ ^ 2 := by
            apply Finset.sum_congr rfl
            intro zOutcome _
            rw [Fintype.sum_eq_single
              (signSyndrome (0 : XCheckIndex → Bit))]
            · simp [historyOutcome_accepted_iff]
            · intro xOutcome hxOutcome
              have hnotaccepted :
                  historyOutcome (zOutcome, xOutcome) ≠ .accepted := by
                intro haccepted
                exact hxOutcome (historyOutcome_accepted_iff zOutcome xOutcome |>.mp
                  haccepted)
              simp [hnotaccepted]
    _ = ∑ word : Word, weight word *
        ∑ zOutcome : ZJointSyndrome,
          ‖historyKraus
            (zOutcome, signSyndrome (0 : XCheckIndex → Bit))
            (bk15ErrorWordState word)‖ ^ 2 := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro word _
              rw [← Finset.mul_sum]
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
set_option linter.constructorNameAsVariable false
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution (epsilon : BK15Epsilon) :
    endpointWeight epsilon .accepted =
      ∑ word ∈ l1DualWords, bk15WordWeight epsilon word := by
  classical
  rw [endpointWeight_eq_history_word_sum,
    accepted_history_word_sum (bk15WordWeight epsilon)]
  simp_rw [accepted_history_mass_eq_l1Dual_indicator_QECertEndpoint]
  have hfilter :
      (Finset.univ.filter fun word : Word => word ∈ l1DualWords) =
        l1DualWords := by
    ext word
    simp
  calc
    ∑ word : Word, bk15WordWeight epsilon word *
        (if word ∈ l1DualWords then 1 else 0) =
      ∑ word : Word,
        if word ∈ l1DualWords then bk15WordWeight epsilon word else 0 := by
          apply Finset.sum_congr rfl
          intro word _
          by_cases hmember : word ∈ l1DualWords <;> simp [hmember]
    _ = ∑ word ∈ Finset.univ.filter
        (fun word : Word => word ∈ l1DualWords),
        bk15WordWeight epsilon word := by
          symm
          rw [Finset.sum_filter]
    _ = ∑ word ∈ l1DualWords, bk15WordWeight epsilon word := by
          rw [hfilter]
end QEC.Distillation.BK15.Recurrence


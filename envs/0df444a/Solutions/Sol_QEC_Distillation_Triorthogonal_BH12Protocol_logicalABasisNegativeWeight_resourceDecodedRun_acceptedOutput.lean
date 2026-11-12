-- Prove2me | solution 1 for QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_resourceDecodedRun_acceptedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:09:48.929234+00:00
-- url     : https://prove2.me/submissions/89087a59-1aaa-4a11-9bc3-cb37a194ae5f

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisInstrument_branch_negative_logicalErrorDensity
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerConditionalDensity_toOperator
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_kraus
import Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerInstrument_observe
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_apply
import Theorems.Thm_QEC_Coding_PauliSymplectic_toHermitianQubitOperator_binaryOne
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_conditionalOutput
import Theorems.Thm_QEC_Distillation_DistillationRun_postprocess_successProbability
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamard_conj_one
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftLinearEquiv_symm_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftTransport_apply
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phase_conj_one
import Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_bitstringWordEquiv_reducedLogicalBits
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_correctedAllSiteT_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_code
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_encodedCode_encoding
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalComputationalState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalMagicState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_logicalPlusState_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_oddWordLinearEquivLogicalQuotient_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_physicalCliffordCorrection_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_rowCoefficientMap_reducedCombination
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordListXor_reducedWordList
import Theorems.Thm_QEC_Distillation_Triorthogonal_BinaryRowFamily_wordTriplePairing_zero_left
import Theorems.Thm_QEC_Distillation_Triorthogonal_CliffordCorrectionAtom_realized_apply
import Theorems.Thm_QEC_Distillation_Triorthogonal_atomAngleSum_append
import Theorems.Thm_QEC_Distillation_Triorthogonal_cliffordCorrection_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_convexCombination_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
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
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_conditionalOutput
attribute [local simp] QEC.Distillation.DistillationRun.postprocess_successProbability
attribute [local simp] QEC.Distillation.OneQubitMagic.hadamard_conj_one
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
attribute [local simp] QEC.Distillation.OneQubitMagic.phase_conj_one
attribute [local simp] QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.bitstringWordEquiv_reducedLogicalBits
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.correctedAllSiteT_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_code
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.encodedCode_encoding
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalComputationalState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalMagicState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.logicalPlusState_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.oddWordLinearEquivLogicalQuotient_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.physicalCliffordCorrection_apply
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.rowCoefficientMap_reducedCombination
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordListXor_reducedWordList
attribute [local simp] QEC.Distillation.Triorthogonal.BinaryRowFamily.wordTriplePairing_zero_left
attribute [local simp] QEC.Distillation.Triorthogonal.CliffordCorrectionAtom.realized_apply
attribute [local simp] QEC.Distillation.Triorthogonal.atomAngleSum_append
attribute [local simp] QEC.Distillation.Triorthogonal.cliffordCorrection_apply
attribute [local simp] QEC.Semantics.DensityOperator.convexCombination_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_complementCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.card_selectedCoordinates
attribute [local simp] QEC.Semantics.FiniteSubsystem.extendLocal_apply_localEmbedding
attribute [local simp] QEC.Semantics.FiniteSubsystem.localEmbedding_apply
attribute [local simp] QEC.Semantics.FiniteSubsystem.selectedPartialTrace_toLinearMap
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
namespace Triorthogonal
namespace BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
private theorem rawMarginalErrorWeight_eq_errorWordSum (q : Nat)
    (p : ErrorParameter) (a : OddRow q) :
    rawMarginalErrorWeight q p a =
      ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error a ≠ 0 then
          errorWordProbability p error else 0 := by
  classical
  unfold rawMarginalErrorWeight rawLogicalErrorWeight
  calc
    (∑ logical : Word (ZMod 2) (OddRow q),
      if logical a = 0 then 0 else
        ∑ error : PhysicalError q,
          if Accepts error ∧ logicalErrorWord error = logical then
            errorWordProbability p error else 0) =
        ∑ logical : Word (ZMod 2) (OddRow q),
          ∑ error : PhysicalError q,
            if logical a = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro logical _
      by_cases hlogical : logical a = 0 <;> simp [hlogical]
    _ = ∑ error : PhysicalError q,
          ∑ logical : Word (ZMod 2) (OddRow q),
            if logical a = 0 then 0 else
              if Accepts error ∧ logicalErrorWord error = logical then
                errorWordProbability p error else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error a ≠ 0 then
          errorWordProbability p error else 0 := by
      apply Finset.sum_congr rfl
      intro error _
      by_cases haccept : Accepts error
      · by_cases hbit : logicalErrorWord error a = 0
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
        · rw [Fintype.sum_eq_single (logicalErrorWord error)]
          · simp [haccept, hbit]
          · intro logical hne
            simp [hne.symm]
      · simp [haccept]
private theorem trace_logicalABasisInstrument_branch_negative_logicalErrorDensity
    {q : Nat} (a : OddRow q)
    (logical : Word (ZMod 2) (OddRow q)) :
    LinearMap.trace Complex (LogicalRegister q)
        ((logicalABasisInstrument a).branchOperator .negative
          (logicalErrorDensity logical).toOperator) =
      if logical a = 0 then 0 else 1 := by
  rw [logicalABasisInstrument_branch_negative_logicalErrorDensity]
  by_cases hbit : logical a = 0
  · rw [if_pos hbit, if_pos hbit]
    norm_num
  · rw [if_neg hbit, if_neg hbit,
      (logicalErrorDensity logical).trace_one]
private theorem trace_logicalABasisBranchLinearMap_negative_logicalErrorDensity
    {q : Nat} (a : OddRow q)
    (logical : Word (ZMod 2) (OddRow q)) :
    LinearMap.trace Complex (LogicalRegister q)
        (logicalABasisBranchLinearMap a .negative
          (logicalErrorDensity logical).toOperator) =
      if logical a = 0 then 0 else 1 :=
  trace_logicalABasisInstrument_branch_negative_logicalErrorDensity a logical
end BH12Protocol
end Triorthogonal
end Distillation
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
namespace QEC.Distillation.Triorthogonal.BH12Protocol
theorem _root_.solution
    (q : Nat) (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (a : OddRow q) :
    logicalABasisNegativeWeight a
        (resourceDecodedRun q (noisyResources q p)).acceptedOutput =
      decodedMarginalError q p hsuccess a := by
  rw [logicalABasisNegativeWeight, FiniteInstrument.bornWeight,
    resourceDecodedRun_acceptedOutput_toOperator_errorWordSum q p hsuccess]
  change Complex.re (LinearMap.trace Complex (LogicalRegister q)
    (logicalABasisBranchLinearMap a .negative
      (((rawSuccessMass q p : Complex)⁻¹) •
        ∑ error : PhysicalError q,
          if Accepts error then
            (errorWordProbability p error : Complex) •
              (logicalErrorDensity (logicalErrorWord error)).toOperator
          else 0))) = _
  simp only [map_smul, map_sum, apply_ite, map_zero]
  simp_rw [trace_logicalABasisBranchLinearMap_negative_logicalErrorDensity]
  have hsum :
      (∑ error : PhysicalError q,
        if Accepts error then
          (errorWordProbability p error : Complex) •
            (if logicalErrorWord error a = 0 then 0 else 1)
        else 0) =
      ((∑ error : PhysicalError q,
        if Accepts error ∧ logicalErrorWord error a ≠ 0 then
          errorWordProbability p error else 0 : ℝ) : Complex) := by
    push_cast
    apply Finset.sum_congr rfl
    intro error _herror
    by_cases haccept : Accepts error
    · by_cases hbit : logicalErrorWord error a = 0 <;>
        simp [haccept, hbit]
    · simp [haccept]
  rw [hsum]
  simp only [decodedMarginalError, dif_pos hsuccess]
  rw [rawMarginalErrorWeight_eq_errorWordSum]
  rw [smul_eq_mul, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  rw [div_eq_mul_inv]
  ring
end QEC.Distillation.Triorthogonal.BH12Protocol

-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Iteration_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:36:29.774194+00:00
-- url     : https://prove2.me/submissions/ede73574-4ad9-437d-b571-207daf2039a5

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_fixed_iff
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_zero
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Iteration_antitone
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


attribute [local simp] QEC.Distillation.BK15.Threshold.bk15Iteration_zero
section
noncomputable section
namespace QEC
namespace Distillation
namespace BK15
namespace Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
private theorem bk15Recurrence_continuousAt (epsilon : Real) :
    ContinuousAt bk15Recurrence epsilon := by
  have hnumerator : ContinuousAt
      (fun input : Real =>
        1 - 15 * bk15Bias input ^ 7 + 15 * bk15Bias input ^ 8 -
          bk15Bias input ^ 15) epsilon := by
    unfold bk15Bias
    fun_prop
  have hdenominator : ContinuousAt
      (fun input : Real => 2 * (1 + 15 * bk15Bias input ^ 8)) epsilon := by
    unfold bk15Bias
    fun_prop
  unfold bk15Recurrence
  exact hnumerator.div hdenominator
    (bk15Recurrence_scaled_denominator_pos epsilon).ne'
namespace BK15SemanticSchedule
end BK15SemanticSchedule
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
    (epsilon : Real) (hpositive : 0 < epsilon)
    (hthreshold : epsilon < epsilonStar) :
    Filter.Tendsto (bk15Iteration epsilon) Filter.atTop (nhds 0) := by
  let sequence : Nat -> Real := bk15Iteration epsilon
  have hinvariant : ∀ rounds,
      0 < sequence rounds ∧ sequence rounds < epsilonStar := by
    intro rounds
    exact bk15Iteration_pos_and_lt_epsilonStar epsilon hpositive hthreshold rounds
  have hanti : Antitone sequence :=
    bk15Iteration_antitone epsilon hpositive hthreshold
  have hbdd : BddBelow (Set.range sequence) := by
    refine ⟨0, ?_⟩
    rintro value ⟨rounds, rfl⟩
    exact (hinvariant rounds).1.le
  let limit : Real := ⨅ rounds, sequence rounds
  have htendsto : Filter.Tendsto sequence Filter.atTop (nhds limit) := by
    exact tendsto_atTop_ciInf hanti hbdd
  have hlimit_nonneg : 0 <= limit := by
    exact le_ciInf fun rounds => (hinvariant rounds).1.le
  have hlimit_le_input : limit <= epsilon := by
    have hle : limit <= sequence 0 := ciInf_le hbdd 0
    simpa [limit, sequence] using hle
  have hlimit_half : limit <= 1 / 2 := by
    linarith [hlimit_le_input, hthreshold, epsilonStar_lt_half]
  have hcontinuous : ContinuousAt bk15Recurrence limit :=
    bk15Recurrence_continuousAt limit
  have hmap : Filter.Tendsto
      (fun rounds => bk15Recurrence (sequence rounds)) Filter.atTop
      (nhds (bk15Recurrence limit)) :=
    hcontinuous.tendsto.comp htendsto
  have hsucc_atTop : Filter.Tendsto (fun rounds : Nat => rounds + 1)
      Filter.atTop Filter.atTop := by
    exact (strictMono_nat_of_lt_succ fun rounds =>
      Nat.lt_succ_self (rounds + 1)).tendsto_atTop
  have hshift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds limit) := htendsto.comp hsucc_atTop
  have hmap_shift : Filter.Tendsto (fun rounds => sequence (rounds + 1))
      Filter.atTop (nhds (bk15Recurrence limit)) := by
    simpa [sequence, bk15Iteration_succ] using hmap
  have hfixed : bk15Recurrence limit = limit :=
    tendsto_nhds_unique hmap_shift hshift
  have hlimit_zero : limit = 0 := by
    rcases (bk15Recurrence_fixed_iff limit hlimit_nonneg hlimit_half).mp hfixed with
      hzero_limit | hthreshold_limit | hhalf_limit
    · exact hzero_limit
    · exfalso
      rw [hthreshold_limit] at hlimit_le_input
      linarith
    · exfalso
      rw [hhalf_limit] at hlimit_le_input
      linarith [hthreshold, epsilonStar_lt_half]
  simpa [sequence, hlimit_zero] using htendsto
end QEC.Distillation.BK15.Threshold

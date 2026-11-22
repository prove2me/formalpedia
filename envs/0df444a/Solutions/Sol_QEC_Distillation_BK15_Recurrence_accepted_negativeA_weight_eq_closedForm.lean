-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.accepted_negativeA_weight_eq_closedForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:25:00.987174+00:00
-- url     : https://prove2.me/submissions/af9197de-a772-4e49-959f-336c876e101a

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_negativeA_weight_eq_l2LogicalCoset_wordSum
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
import Theorems.Thm_QEC_Distillation_BK15_l2LogicalCoset_weight_enumerator
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
private theorem bk15WordWeight_eq_hammingWeight
    (epsilon : BK15Epsilon) (word : Word) :
    bk15WordWeight epsilon word =
      epsilon.epsilon ^ Coding.HammingWeight word *
        epsilon.cleanWeight ^ (15 - Coding.HammingWeight word) := by
  classical
  have hfactor : ∀ site : Fin 15,
      aInputWeight epsilon (word site) =
        if word site = 0 then epsilon.cleanWeight else epsilon.epsilon := by
    intro site
    generalize hbit : word site = bit
    fin_cases bit <;> rfl
  unfold bk15WordWeight
  simp_rw [hfactor]
  rw [Finset.prod_ite]
  have hnonzero :
      (Finset.univ.filter fun site : Fin 15 => ¬ word site = 0) =
        Coding.hammingSupport word := by
    ext site
    simp [Coding.hammingSupport]
  have hzeroCard :
      (Finset.univ.filter fun site : Fin 15 => word site = 0).card =
        15 - Coding.HammingWeight word := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (fun site : Fin 15 => word site = 0)
    rw [hnonzero, ← Coding.HammingWeight_eq_card_hammingSupport] at hpartition
    have hunivCard : (Finset.univ : Finset (Fin 15)).card = 15 := by simp
    rw [hunivCard] at hpartition
    exact Nat.eq_sub_of_add_eq hpartition
  have hnonzeroCard :
      (Finset.univ.filter fun site : Fin 15 => ¬ word site = 0).card =
        Coding.HammingWeight word := by
    rw [hnonzero, Coding.HammingWeight_eq_card_hammingSupport]
  rw [Finset.prod_const, Finset.prod_const, hzeroCard, hnonzeroCard]
  ring
private theorem sum_bk15WordWeight_eq_weightEnumerator
    (epsilon : BK15Epsilon) (words : Finset Word) :
    ∑ word ∈ words, bk15WordWeight epsilon word =
      ∑ weight : Fin 16,
        (weightCount words weight.1 : Real) *
          (epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1)) := by
  classical
  calc
    ∑ word ∈ words, bk15WordWeight epsilon word =
        ∑ weight : Fin 16, ∑ word ∈ words with bk15WeightIndex word = weight,
          bk15WordWeight epsilon word := by
            symm
            exact Finset.sum_fiberwise_of_maps_to
              (fun word _ => Finset.mem_univ _) _
    _ = ∑ weight : Fin 16,
        (weightCount words weight.1 : Real) *
          (epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1)) := by
            apply Finset.sum_congr rfl
            intro weight _
            have hfilter :
                words.filter (fun word => bk15WeightIndex word = weight) =
                  words.filter (fun word => Coding.HammingWeight word = weight.1) := by
              ext word
              simp only [Finset.mem_filter]
              exact and_congr_right (fun _ => Fin.ext_iff)
            rw [show (∑ word ∈ words with bk15WeightIndex word = weight,
                bk15WordWeight epsilon word) =
                ∑ word ∈ words with bk15WeightIndex word = weight,
                  epsilon.epsilon ^ weight.1 * epsilon.cleanWeight ^ (15 - weight.1) by
                apply Finset.sum_congr rfl
                intro word hword
                rw [Finset.mem_filter] at hword
                rw [bk15WordWeight_eq_hammingWeight]
                have hweight : Coding.HammingWeight word = weight.1 := by
                  simpa [bk15WeightIndex, Fin.ext_iff] using hword.2
                rw [hweight]]
            rw [Finset.sum_const, nsmul_eq_mul, hfilter]
            rfl
private theorem l2LogicalCoset_wordWeight_sum_expanded (epsilon : BK15Epsilon) :
    ∑ word ∈ l2LogicalCosetWords, bk15WordWeight epsilon word =
      35 * (epsilon.epsilon ^ 3 * epsilon.cleanWeight ^ 12) +
        168 * (epsilon.epsilon ^ 5 * epsilon.cleanWeight ^ 10) +
        435 * (epsilon.epsilon ^ 7 * epsilon.cleanWeight ^ 8) +
        280 * (epsilon.epsilon ^ 9 * epsilon.cleanWeight ^ 6) +
        105 * (epsilon.epsilon ^ 11 * epsilon.cleanWeight ^ 4) +
        epsilon.epsilon ^ 15 := by
  rw [sum_bk15WordWeight_eq_weightEnumerator]
  simp [Fin.sum_univ_succ, l2LogicalCoset_weight_enumerator]
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
set_option linter.constructorNameAsVariable false
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution (epsilon : BK15Epsilon) :
    acceptedNegativeAWeight epsilon =
      (1 - 15 * bk15_r epsilon ^ 7 + 15 * bk15_r epsilon ^ 8 -
        bk15_r epsilon ^ 15) / 32 := by
  rw [accepted_negativeA_weight_eq_l2LogicalCoset_wordSum,
    l2LogicalCoset_wordWeight_sum_expanded]
  unfold bk15_r BK15Epsilon.cleanWeight
  ring
end QEC.Distillation.BK15.Recurrence

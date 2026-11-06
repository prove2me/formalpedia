-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_coordinateOperator_branchOperator_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:07:05.392483+00:00
-- url     : https://prove2.me/submissions/d1323eb2-29c3-4cc4-b66b-756e32c7c16d

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_branchOperator_fst_sum_partialTraceRight
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_branchOperator_snd_sum_partialTraceLeft
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_leftMarginal_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_partialTraceRightRaw_mapDensity_tensorDensity
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
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
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
attribute [local simp] QEC.Semantics.FiniteInstrument.leftMarginal_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.partialTraceRightRaw_mapDensity_tensorDensity
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerInputMarginal_productInput
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_symm_at
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_symm_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedPartialTraceChannel_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerSelectedRegisterReindex_apply_basis
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.log2Matrix_apply
attribute [local simp] QEC.Semantics.FiniteMatrixEntropy.logMatrix_apply
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



set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (A : Operator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      tensorPowerCoordinateOperator attempts trial
          (∑ history : tensorPowerHistory Omega attempts,
            if tensorPowerHistoryAt Omega attempts history trial = outcome then
              (I.tensorPower attempts).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (tensorPowerCoordinateOperator attempts trial A) := by
  intro attempts
  induction attempts with
  | zero =>
      intro A trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro A trial outcome
      refine Fin.cases ?_ ?_ trial
      · have hsum :
          (∑ history : Omega × tensorPowerHistory Omega attempts,
              if history.1 = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              (I.tensor (I.tensorPower attempts)).branchOperator
                (outcome, tail) A := by
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_eq_single outcome]
            · apply Finset.sum_congr rfl
              intro tail _
              exact if_pos rfl
            · intro x _ hx
              apply Finset.sum_eq_zero
              intro tail _
              exact if_neg hx
            · intro hout
              exact (hout (Finset.mem_univ _)).elim
        change partialTraceRightRaw K (tensorPowerCarrier K attempts)
            (∑ history : Omega × tensorPowerHistory Omega attempts,
              if history.1 = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
          I.branchOperator outcome
            (partialTraceRightRaw H (tensorPowerCarrier H attempts) A)
        rw [hsum]
        exact tensor_branchOperator_fst_sum_partialTraceRight
          I (I.tensorPower attempts) (I.tensorPower_complete hI attempts)
          outcome A
      · intro tailTrial
        let tailInput := FiniteMatrixEntropy.partialTraceLeftRaw
          H (tensorPowerCarrier H attempts) A
        have hsum :
          (∑ history : Omega × tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
                (I.tensor (I.tensorPower attempts)).branchOperator history A
              else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                ∑ head : Omega,
                  (I.tensor (I.tensorPower attempts)).branchOperator (head, tail) A
              else 0 := by
            rw [Fintype.sum_prod_type, Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · simp [htail]
            · simp [htail]
        have hmarginal :
          FiniteMatrixEntropy.partialTraceLeftRaw K
              (tensorPowerCarrier K attempts)
              (∑ tail : tensorPowerHistory Omega attempts,
                if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                  ∑ head : Omega,
                    (I.tensor (I.tensorPower attempts)).branchOperator
                      (head, tail) A
                else 0) =
            ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                (I.tensorPower attempts).branchOperator tail tailInput
              else 0 := by
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · rw [if_pos htail, if_pos htail]
              exact tensor_branchOperator_snd_sum_partialTraceLeft
                I hI (I.tensorPower attempts) tail A
            · simp [htail]
        change tensorPowerCoordinateOperator attempts tailTrial
            (FiniteMatrixEntropy.partialTraceLeftRaw K
              (tensorPowerCarrier K attempts)
              (∑ history : Omega × tensorPowerHistory Omega attempts,
                if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
                  (I.tensor (I.tensorPower attempts)).branchOperator history A
                else 0)) =
          I.branchOperator outcome
            (tensorPowerCoordinateOperator attempts tailTrial tailInput)
        rw [hsum, hmarginal]
        exact ih tailInput tailTrial outcome
end QEC.Semantics.FiniteInstrument

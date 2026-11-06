-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_coordinate_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:03:55.849463+00:00
-- url     : https://prove2.me/submissions/5b287e91-7850-4a98-bf12-1c59593b5391

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_bornWeight_fst_sum_eq_partialTraceRight
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_bornWeight_snd_sum_eq_leftMarginal
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_mem_tensorPowerObservedAcceptedIndices
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
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
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.mem_tensorPowerObservedAcceptedIndices
attribute [local simp] QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_succ_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
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
open scoped BigOperators TensorProduct
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
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts) (outcome : Omega),
      (∑ history : tensorPowerHistory Omega attempts,
        if tensorPowerHistoryAt Omega attempts history trial = outcome then
          (I.tensorPower attempts).bornWeight history rho
        else 0) =
        I.bornWeight outcome (tensorPowerInputMarginal attempts rho trial) := by
  intro attempts
  induction attempts with
  | zero =>
      intro rho trial
      exact Fin.elim0 trial
  | succ attempts ih =>
      intro rho trial outcome
      refine Fin.cases ?_ ?_ trial
      · change
          (∑ history : Omega × tensorPowerHistory Omega attempts,
            if history.1 = outcome then
              (I.tensor (I.tensorPower attempts)).bornWeight history rho
            else 0) =
            I.bornWeight outcome
              (partialTraceRightRaw_mapDensity H
                (tensorPowerCarrier H attempts) rho)
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ head : Omega,
              if head = outcome then
                ∑ tail : tensorPowerHistory Omega attempts,
                  (I.tensor (I.tensorPower attempts)).bornWeight (head, tail) rho
              else 0 := by
            apply Finset.sum_congr rfl
            intro head _
            by_cases hhead : head = outcome
            · simp [hhead]
            · simp [hhead]
          _ = ∑ head : Omega,
              if head = outcome then
                I.bornWeight head
                  (partialTraceRightRaw_mapDensity H
                    (tensorPowerCarrier H attempts) rho)
              else 0 := by
            apply Finset.sum_congr rfl
            intro head _
            by_cases hhead : head = outcome
            · rw [if_pos hhead, if_pos hhead,
                tensor_bornWeight_fst_sum_eq_partialTraceRight I
                  (I.tensorPower attempts) (I.tensorPower_complete hI attempts)]
            · simp [hhead]
          _ = _ := by simp
      · intro tailTrial
        change
          (∑ history : Omega × tensorPowerHistory Omega attempts,
            if tensorPowerHistoryAt Omega attempts history.2 tailTrial = outcome then
              (I.tensor (I.tensorPower attempts)).bornWeight history rho
            else 0) =
            I.bornWeight outcome
              (tensorPowerInputMarginal attempts
                (DensityOperator.leftMarginal rho) tailTrial)
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        calc
          _ = ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                ∑ head : Omega,
                  (I.tensor (I.tensorPower attempts)).bornWeight (head, tail) rho
              else 0 := by
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · simp [htail]
            · simp [htail]
          _ = ∑ tail : tensorPowerHistory Omega attempts,
              if tensorPowerHistoryAt Omega attempts tail tailTrial = outcome then
                (I.tensorPower attempts).bornWeight tail
                  (DensityOperator.leftMarginal rho)
              else 0 := by
            apply Finset.sum_congr rfl
            intro tail _
            by_cases htail :
                tensorPowerHistoryAt Omega attempts tail tailTrial = outcome
            · rw [if_pos htail, if_pos htail,
                tensor_bornWeight_snd_sum_eq_leftMarginal I hI]
            · simp [htail]
          _ = _ := ih (DensityOperator.leftMarginal rho) tailTrial outcome
end QEC.Semantics.FiniteInstrument

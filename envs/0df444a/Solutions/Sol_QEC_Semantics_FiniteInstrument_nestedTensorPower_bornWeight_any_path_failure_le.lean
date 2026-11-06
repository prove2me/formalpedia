-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorPower_bornWeight_any_path_failure_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:24:48.395306+00:00
-- url     : https://prove2.me/submissions/7e556cdd-6834-40d4-bf4b-251106ac3bd3

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_bornWeight_path_failure_sum_eq
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
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
universe u v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (fails : Omega -> Prop) [DecidablePred fails]
    (branches depth : Nat)
    (rho : DensityOperator (nestedTensorCarrier H branches depth)) :
    (∑ history ∈ Finset.univ.filter
        (fun history : nestedTensorHistory Omega branches depth =>
          ∃ path : nestedTensorPath branches depth,
            fails (nestedTensorHistoryAt Omega branches depth history path)),
      (nestedTensorPower I branches depth).bornWeight history rho) ≤
      ∑ path : nestedTensorPath branches depth,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ history : nestedTensorHistory Omega branches depth,
        if (∃ path : nestedTensorPath branches depth,
              fails (nestedTensorHistoryAt Omega branches depth history path)) then
          (nestedTensorPower I branches depth).bornWeight history rho
        else 0) ≤
        ∑ history : nestedTensorHistory Omega branches depth,
          ∑ path : nestedTensorPath branches depth,
            if fails (nestedTensorHistoryAt Omega branches depth history path) then
              (nestedTensorPower I branches depth).bornWeight history rho
            else 0 := by
      apply Finset.sum_le_sum
      intro history _
      by_cases hfailure :
          ∃ path : nestedTensorPath branches depth,
            fails (nestedTensorHistoryAt Omega branches depth history path)
      · rw [if_pos hfailure]
        obtain ⟨path, hpath⟩ := hfailure
        simpa [hpath] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset (nestedTensorPath branches depth)))
            (f := fun other : nestedTensorPath branches depth =>
              if fails (nestedTensorHistoryAt Omega branches depth history other) then
                (nestedTensorPower I branches depth).bornWeight history rho
              else 0)
            (fun other _ => by
              by_cases hother :
                  fails (nestedTensorHistoryAt Omega branches depth history other)
              · simpa [hother] using
                  (nestedTensorPower I branches depth).bornWeight_nonneg history rho
              · simp [hother])
            (Finset.mem_univ path))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun path _ => by
          by_cases hpath :
              fails (nestedTensorHistoryAt Omega branches depth history path)
          · simpa [hpath] using
              (nestedTensorPower I branches depth).bornWeight_nonneg history rho
          · simp [hpath]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ history : nestedTensorHistory Omega branches depth,
          if fails (nestedTensorHistoryAt Omega branches depth history path) then
            (nestedTensorPower I branches depth).bornWeight history rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ outcome ∈ Finset.univ.filter fails,
          I.bornWeight outcome
            (nestedTensorInputMarginal H branches depth rho path) := by
      apply Finset.sum_congr rfl
      intro path _
      rw [← Finset.sum_filter]
      exact nestedTensorPower_bornWeight_path_failure_sum_eq
        I hI fails branches depth rho path
end QEC.Semantics.FiniteInstrument

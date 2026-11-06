-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensor_coordinateOperator_branchOperator_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:12.200894+00:00
-- url     : https://prove2.me/submissions/5ec74b9c-943e-4890-a031-21ecc220e9d2

import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_MarginalBranchOperator
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_coordinateOperator_branchOperator_sum_eq
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
    (branches : Nat) :
    ∀ (depth : Nat) (A : Operator (nestedTensorCarrier H branches depth))
      (path : nestedTensorPath branches depth) (outcome : Omega),
      nestedTensorCoordinateOperator K branches depth path
          (∑ history : nestedTensorHistory Omega branches depth,
            if nestedTensorHistoryAt Omega branches depth history path = outcome then
              (nestedTensorPower I branches depth).branchOperator history A
            else 0) =
        I.branchOperator outcome
          (nestedTensorCoordinateOperator H branches depth path A) := by
  intro depth
  induction depth generalizing kappa Omega H K with
  | zero =>
      intro A path outcome
      have hpath : path = PUnit.unit := PUnit.ext _ _
      subst path
      change (∑ history : Omega,
        if history = outcome then I.branchOperator history A else 0) =
          I.branchOperator outcome A
      erw [Fintype.sum_eq_single outcome]
      · exact if_pos rfl
      · intro other hother
        exact if_neg hother
  | succ depth ih =>
      intro A path outcome
      rcases path with ⟨pathPrefix, trial⟩
      let prefixInput :=
        nestedTensorCoordinateOperator
          (tensorPowerCarrier H branches) branches depth pathPrefix A
      have hregroup :
          (∑ history : nestedTensorHistory
              (tensorPowerHistory Omega branches) branches depth,
            if tensorPowerHistoryAt Omega branches
                (nestedTensorHistoryAt
                  (tensorPowerHistory Omega branches) branches depth
                  history pathPrefix) trial = outcome then
              (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                history A
            else 0) =
            ∑ layer : tensorPowerHistory Omega branches,
              if tensorPowerHistoryAt Omega branches layer trial = outcome then
                ∑ history : nestedTensorHistory
                    (tensorPowerHistory Omega branches) branches depth,
                  if nestedTensorHistoryAt
                      (tensorPowerHistory Omega branches) branches depth
                      history pathPrefix = layer then
                    (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                      history A
                  else 0
              else 0 := by
        calc
          _ = ∑ history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth,
              ∑ layer : tensorPowerHistory Omega branches,
                if tensorPowerHistoryAt Omega branches layer trial = outcome ∧
                    nestedTensorHistoryAt
                      (tensorPowerHistory Omega branches) branches depth
                      history pathPrefix = layer then
                  (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                    history A
                else 0 := by
              apply Finset.sum_congr rfl
              intro history _
              rw [Fintype.sum_eq_single
                (nestedTensorHistoryAt
                  (tensorPowerHistory Omega branches) branches depth
                  history pathPrefix)]
              · simp
              · intro layer hne
                simp [hne.symm]
          _ = ∑ layer : tensorPowerHistory Omega branches,
                ∑ history : nestedTensorHistory
                    (tensorPowerHistory Omega branches) branches depth,
                  if tensorPowerHistoryAt Omega branches layer trial = outcome ∧
                      nestedTensorHistoryAt
                        (tensorPowerHistory Omega branches) branches depth
                        history pathPrefix = layer then
                    (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                      history A
                  else 0 := by
              rw [Finset.sum_comm]
          _ = _ := by
              apply Finset.sum_congr rfl
              intro layer _
              by_cases hlayer :
                  tensorPowerHistoryAt Omega branches layer trial = outcome
              · simp [hlayer]
              · simp [hlayer]
      have hprefix :
          nestedTensorCoordinateOperator
              (tensorPowerCarrier K branches) branches depth pathPrefix
              (∑ layer : tensorPowerHistory Omega branches,
                if tensorPowerHistoryAt Omega branches layer trial = outcome then
                  ∑ history : nestedTensorHistory
                      (tensorPowerHistory Omega branches) branches depth,
                    if nestedTensorHistoryAt
                        (tensorPowerHistory Omega branches) branches depth
                        history pathPrefix = layer then
                      (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                        history A
                    else 0
                else 0) =
            ∑ layer : tensorPowerHistory Omega branches,
              if tensorPowerHistoryAt Omega branches layer trial = outcome then
                (I.tensorPower branches).branchOperator layer prefixInput
              else 0 := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro layer _
        by_cases hlayer :
            tensorPowerHistoryAt Omega branches layer trial = outcome
        · rw [if_pos hlayer, if_pos hlayer]
          simpa [prefixInput] using
            (ih
              (I := I.tensorPower branches)
              (hI := I.tensorPower_complete hI branches)
              (A := A) (path := pathPrefix) (outcome := layer))
        · simp [hlayer]
      change
        tensorPowerCoordinateOperator branches trial
          (nestedTensorCoordinateOperator
            (tensorPowerCarrier K branches) branches depth pathPrefix
            (∑ history : nestedTensorHistory
                (tensorPowerHistory Omega branches) branches depth,
              if tensorPowerHistoryAt Omega branches
                  (nestedTensorHistoryAt
                    (tensorPowerHistory Omega branches) branches depth
                    history pathPrefix) trial = outcome then
                (nestedTensorPower (I.tensorPower branches) branches depth).branchOperator
                  history A
              else 0)) =
          I.branchOperator outcome
            (tensorPowerCoordinateOperator branches trial prefixInput)
      rw [hregroup, hprefix]
      exact tensorPower_coordinateOperator_branchOperator_sum_eq
        I hI branches prefixInput trial outcome
end QEC.Semantics.FiniteInstrument

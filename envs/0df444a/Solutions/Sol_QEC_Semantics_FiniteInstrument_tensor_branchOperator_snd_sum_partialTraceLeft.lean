-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensor_branchOperator_snd_sum_partialTraceLeft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:04:10.873213+00:00
-- url     : https://prove2.me/submissions/9789008b-7a9a-498d-8178-bcd69250bf2c

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
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
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_branchOperator_eq_inducedMap
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_succ_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerInputMarginal_productInput
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_symm_at
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_symm_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedPartialTraceChannel_apply
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerSelectedRegisterReindex_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_inducedMap_partialTraceLeft
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


section
universe u v w x y
namespace QEC
namespace Semantics
open Classical
open scoped BigOperators
noncomputable section
namespace FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]
private theorem outcomeBranchInstrument_inducedMap
    (I : FiniteInstrument kappa Omega H K) (outcome : Omega)
    (A : Operator H) :
    (outcomeBranchInstrument I outcome).kraus.inducedMap A =
      I.branchOperator outcome A := by
  classical
  rw [FiniteKrausFamily.inducedMap_apply]
  unfold branchOperator outcomeBranchInstrument
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : I.observe index = outcome
  · simp [hindex]
  · simp [hindex]
private theorem tensor_outcomeBranchInstrument_branchOperator
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome rightOutcome : Xi) (leftOutcome : Omega)
    (A : Operator (CompositeSystem H R)) :
    (I.tensor (outcomeBranchInstrument J outcome)).branchOperator
        (leftOutcome, rightOutcome) A =
      if rightOutcome = outcome then
        (I.tensor J).branchOperator (leftOutcome, outcome) A
      else 0 := by
  classical
  by_cases houtcome : rightOutcome = outcome
  · subst rightOutcome
    rw [if_pos rfl]
    unfold branchOperator
    apply Finset.sum_congr rfl
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hright : J.observe rightIndex = outcome
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]
  · rw [if_neg houtcome]
    unfold branchOperator
    apply Finset.sum_eq_zero
    rintro ⟨leftIndex, rightIndex⟩ _
    by_cases hright : J.observe rightIndex = outcome
    · have hreverse : outcome ≠ rightOutcome := by
        exact fun equality => houtcome equality.symm
      simp [outcomeBranchInstrument, FiniteInstrument.tensor, hreverse]
    · simp [outcomeBranchInstrument, FiniteInstrument.tensor, hright]
private theorem tensor_outcomeBranchInstrument_inducedMap
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Xi) (A : Operator (CompositeSystem H R)) :
    (I.tensor (outcomeBranchInstrument J outcome)).kraus.inducedMap A =
      ∑ leftOutcome : Omega,
        (I.tensor J).branchOperator (leftOutcome, outcome) A := by
  classical
  rw [← FiniteInstrument.sum_branchOperator_eq_inducedMap
    (I.tensor (outcomeBranchInstrument J outcome)) A]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  calc
    (∑ rightOutcome : Xi, ∑ leftOutcome : Omega,
        (I.tensor (outcomeBranchInstrument J outcome)).branchOperator
          (leftOutcome, rightOutcome) A) =
        ∑ rightOutcome : Xi,
          if rightOutcome = outcome then
            ∑ leftOutcome : Omega,
              (I.tensor J).branchOperator (leftOutcome, outcome) A
          else 0 := by
            apply Finset.sum_congr rfl
            intro rightOutcome _
            by_cases hright : rightOutcome = outcome
            · rw [if_pos hright]
              apply Finset.sum_congr rfl
              intro leftOutcome _
              simpa [hright] using
                tensor_outcomeBranchInstrument_branchOperator
                  I J outcome rightOutcome leftOutcome A
            · rw [if_neg hright]
              apply Finset.sum_eq_zero
              intro leftOutcome _
              rw [tensor_outcomeBranchInstrument_branchOperator]
              simp [hright]
    _ = _ := by simp
end FiniteInstrument
end
end Semantics
end QEC
end

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
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Xi) (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        (∑ leftOutcome : Omega,
          (I.tensor J).branchOperator (leftOutcome, outcome) A) =
      J.branchOperator outcome
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by
  rw [← tensor_outcomeBranchInstrument_inducedMap I J outcome A]
  rw [tensor_inducedMap_partialTraceLeft
    I (outcomeBranchInstrument J outcome) hI]
  exact outcomeBranchInstrument_inducedMap J outcome _
end QEC.Semantics.FiniteInstrument

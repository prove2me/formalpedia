-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bind_nestedTensor_bornWeight_first_and_any_path_failure_le_filteredBranchTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:26:07.6639+00:00
-- url     : https://prove2.me/submissions/989e2e9a-0c33-4c42-9010-b162d186d95f

import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_nonneg
import Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_zero
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
attribute [local simp] QEC.Semantics.FiniteInstrument.branchOperator_zero
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
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (rho : DensityOperator H) :
    (∑ outcome ∈ Finset.univ.filter
        (fun outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth =>
          firstPredicate outcome.1 ∧
            ∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)),
      (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
        outcome rho) <=
      ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              firstPredicate path rho.toOperator))) := by
  classical
  rw [Finset.sum_filter]
  calc
    (∑ outcome : Sigma fun _ : Omega =>
          nestedTensorHistory Xi branches depth,
        if firstPredicate outcome.1 ∧
            (∃ path : nestedTensorPath branches depth,
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)) then
          (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
            outcome rho
        else 0) <=
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          ∑ path : nestedTensorPath branches depth,
            if firstPredicate outcome.1 ∧
                secondPredicate
                  (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
              (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                outcome rho
            else 0 := by
      apply Finset.sum_le_sum
      intro outcome _
      by_cases hfailure : firstPredicate outcome.1 ∧
          ∃ path : nestedTensorPath branches depth,
            secondPredicate
              (nestedTensorHistoryAt Xi branches depth outcome.2 path)
      · rw [if_pos hfailure]
        obtain ⟨hfirst, path, hpath⟩ := hfailure
        simpa [hfirst, hpath] using
          (Finset.single_le_sum
            (s := (Finset.univ : Finset
              (nestedTensorPath branches depth)))
            (f := fun other : nestedTensorPath branches depth =>
              if firstPredicate outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other) then
                (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
                  outcome rho
              else 0)
            (fun other _ => by
              by_cases hother : firstPredicate outcome.1 ∧
                  secondPredicate
                    (nestedTensorHistoryAt Xi branches depth outcome.2 other)
              · simpa [hother] using
                  (I.bind
                    (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                      outcome rho
              · simp [hother])
            (Finset.mem_univ path))
      · rw [if_neg hfailure]
        exact Finset.sum_nonneg fun path _ => by
          by_cases hpath : firstPredicate outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path)
          · simpa [hpath] using
              (I.bind
                (fun _ => nestedTensorPower J branches depth)).bornWeight_nonneg
                  outcome rho
          · simp [hpath]
    _ = ∑ path : nestedTensorPath branches depth,
        ∑ outcome : Sigma fun _ : Omega =>
            nestedTensorHistory Xi branches depth,
          if firstPredicate outcome.1 ∧
              secondPredicate
                (nestedTensorHistoryAt Xi branches depth outcome.2 path) then
            (I.bind (fun _ => nestedTensorPower J branches depth)).bornWeight
              outcome rho
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (bindNestedFilteredCoordinateOperator branches depth I J
            firstPredicate secondPredicate path rho.toOperator)) := by
      apply Finset.sum_congr rfl
      intro path _
      exact
        (bindNestedFilteredCoordinateOperator_trace_re_eq_bornWeight_sum
          branches depth I J firstPredicate secondPredicate path rho).symm
    _ = ∑ path : nestedTensorPath branches depth,
        Complex.re (LinearMap.trace Complex L
          (filteredBranchOperatorSum J secondPredicate
            (nestedFilteredPredecessorCoordinateOperator branches depth I
              firstPredicate path rho.toOperator))) := by
      apply Finset.sum_congr rfl
      intro path _
      rw [bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
        branches depth I J hJ firstPredicate secondPredicate path rho.toOperator]
end QEC.Semantics.FiniteInstrument

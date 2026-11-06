-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.projectorProductOn_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:53:11.482085+00:00
-- url     : https://prove2.me/submissions/1dba73ad-34a5-46a1-a0d1-31f4a9411c02

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projector_is_idempotent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.regionSubsystem_selected
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.tensorDensity_toOperator
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
attribute [local simp] QEC.Semantics.QuditSubsystem.registerFactorizationWithReference_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.replacementFactorizedKraus_operator
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceReordering_apply_tmul
attribute [local simp] QEC.Semantics.QuditSubsystem.selectedReferenceTransport_apply_tmul
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (M : BPTCommutingProjectorModel L kappa)
    (checks : Finset kappa) :
    (M.projectorProductOn checks).comp (M.projectorProductOn checks) =
      M.projectorProductOn checks := by
  classical
  induction checks using Finset.induction_on with
  | empty =>
      change (1 : Semantics.Operator L.Register).comp 1 = 1
      ext x
      rfl
  | insert check checks hnotmem induction =>
      have hrest : (checks : Set kappa).Pairwise (Function.onFun Commute M.projector) :=
        (M.projectorPairwiseCommute (insert check checks)).mono
          (fun _ hmem => Finset.mem_insert_of_mem hmem)
      let productRest := checks.noncommProd M.projector hrest
      have hfactor : (insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks)) =
          M.projector check * productRest := by
        rw [Finset.noncommProd_insert_of_notMem checks check M.projector
          (M.projectorPairwiseCommute (insert check checks)) hnotmem]
      have hcommRest : Commute (M.projector check) productRest := by
        dsimp [productRest]
        exact Finset.noncommProd_commute checks M.projector hrest (M.projector check)
          (fun other _ => M.projector_commute check other)
      have hidempotentRest : productRest * productRest = productRest := by
        dsimp [productRest]
        simpa [projectorProductOn, Module.End.mul_eq_comp] using induction
      change ((insert check checks).noncommProd M.projector
          (M.projectorPairwiseCommute (insert check checks))) *
          ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) = _
      calc
        ((insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks))) *
            ((insert check checks).noncommProd M.projector
              (M.projectorPairwiseCommute (insert check checks))) =
            (M.projector check * productRest) * (M.projector check * productRest) := by
              rw [hfactor]
        _ = M.projector check * ((productRest * M.projector check) * productRest) := by
              simp only [mul_assoc]
        _ = M.projector check * ((M.projector check * productRest) * productRest) := by
              rw [hcommRest.eq]
        _ = (M.projector check * M.projector check) * (productRest * productRest) := by
              simp only [mul_assoc]
        _ = M.projector check * productRest := by
              rw [show M.projector check * M.projector check = M.projector check by
                simpa [Module.End.mul_eq_comp] using M.projector_is_idempotent check,
                hidempotentRest]
        _ = (insert check checks).noncommProd M.projector
            (M.projectorPairwiseCommute (insert check checks)) := hfactor.symm
end QEC.Bounds.BPTCommutingProjectorModel

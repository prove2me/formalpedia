-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.encodedQubits_le_squarePartitionC_card_mul_log_uniformDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:43:46.427475+00:00
-- url     : https://prove2.me/submissions/d252d777-34d3-4a98-9c51-ba128cd7ae53

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_rectangle_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_symm
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionAB_eq_compl_C
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_encodedQubits_le_squarePartition_complement_log_dimensions
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_sum_log_selectedDimensions_le_card_mul_log_uniformDimension
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.mem_regionSubsystem_selected_iff
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.productBlockRegrouping_apply_tmul_tmul
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


attribute [local simp] QEC.Bounds.BPTSquareLattice.mem_rectangle_iff

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (blockWidth margin : Nat)
    (hA : M.RegionErasureRecoverable (L.lattice.squarePartitionA blockWidth margin))
    (hB : M.RegionErasureRecoverable (L.lattice.squarePartitionB blockWidth margin)) :
    (parameter.encodedQubits : Real) ≤
      ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) := by
  let A := L.lattice.squarePartitionA blockWidth margin
  let B := L.lattice.squarePartitionB blockWidth margin
  let C := L.lattice.squarePartitionC blockWidth margin
  let U := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem
    (M.regionSubsystem A) (M.regionSubsystem B)
  let e : {site : L.Site // site ∈ C} ≃ U.ComplementCoordinates :=
    Equiv.subtypeEquivRight fun site => by
      change site ∈ C ↔ site ∉ A ∪ B
      rw [L.lattice.squarePartitionAB_eq_compl_C]
      simp [C]
  have hentropy := M.encodedQubits_le_squarePartition_complement_log_dimensions
    parameter blockWidth margin hA hB
  have hsumSubtype : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site : {site : L.Site // site ∈ C},
        Real.logb 2 (L.localDimension site : Real) := by
    symm
    exact Equiv.sum_comp e (fun site => Real.logb 2 (L.localDimension site : Real))
  have hsubtypeSum : (∑ site : {site : L.Site // site ∈ C},
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) := by
    exact (Finset.sum_subtype C (fun _ => Iff.rfl)
      (fun site => Real.logb 2 (L.localDimension site : Real))).symm
  have hsum : (∑ site : U.ComplementCoordinates,
      Real.logb 2 (L.localDimension site : Real)) =
      ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) :=
    hsumSubtype.trans hsubtypeSum
  have huniform : (∑ site ∈ C, Real.logb 2 (L.localDimension site : Real)) ≤
      (C.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := by
    have hselected := (M.regionSubsystem C).sum_log_selectedDimensions_le_card_mul_log_uniformDimension
      L.localDimension_positive L.uniformDimensionBound
        (fun site _ => L.localDimension_le_uniform site)
    simpa only [M.regionSubsystem_selected] using hselected
  change (parameter.encodedQubits : Real) ≤
    ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
      Real.logb 2 (L.uniformDimensionBound : Real)
  calc
    (parameter.encodedQubits : Real) ≤ ∑ site : U.ComplementCoordinates,
        Real.logb 2 (L.localDimension site : Real) := by
      simpa [A, B, U] using hentropy
    _ = ∑ site ∈ C, Real.logb 2 (L.localDimension site : Real) := hsum
    _ ≤ (C.card : Real) * Real.logb 2 (L.uniformDimensionBound : Real) := huniform
    _ = ((L.lattice.squarePartitionC blockWidth margin).card : Real) *
        Real.logb 2 (L.uniformDimensionBound : Real) := by rfl
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:36:32.310178+00:00
-- url     : https://prove2.me/submissions/4f539f75-cce3-4aaf-9d64-ff859c4f63e7

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_rectangle_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_rectangle_card_le_area
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
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) :
    (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
      36 * margin * margin := by
  let side := margin + margin + margin
  have hLowerLower :
      (L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
        side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hLowerUpper :
      (L.rectangle (index.1 * blockWidth - margin,
        index.2 * blockWidth + blockWidth - margin - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hUpperLower :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hUpperUpper :
      (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
        index.2 * blockWidth + blockWidth - margin - margin) side side).card ≤ side * side :=
    L.rectangle_card_le_area _ _ _
  have hcover : (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
      side * side + side * side + side * side + side * side := by
    calc
      (L.cornerCutoutTileExpandedCover blockWidth margin index).card =
          (((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
            side side ∪
            L.rectangle (index.1 * blockWidth - margin,
              index.2 * blockWidth + blockWidth - margin - margin) side side) ∪
              L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth - margin) side side) ∪
                L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                  index.2 * blockWidth + blockWidth - margin - margin) side side).card := rfl
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side ∪
          L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side) ∪
            L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side ∪
          L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.rectangle (index.1 * blockWidth - margin, index.2 * blockWidth - margin)
          side side).card +
          (L.rectangle (index.1 * blockWidth - margin,
            index.2 * blockWidth + blockWidth - margin - margin) side side).card +
            (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
              index.2 * blockWidth - margin) side side).card) +
              (L.rectangle (index.1 * blockWidth + blockWidth - margin - margin,
                index.2 * blockWidth + blockWidth - margin - margin) side side).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ (side * side + side * side + side * side) + side * side := by
        gcongr
      _ = side * side + side * side + side * side + side * side := by omega
  calc
    (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
        side * side + side * side + side * side + side * side := hcover
    _ = 36 * margin * margin := by dsimp [side]; ring
end QEC.Bounds.BPTSquareLattice

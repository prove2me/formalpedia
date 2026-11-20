-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_even_cornerCutoutComponents
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:44:30.743825+00:00
-- url     : https://prove2.me/submissions/454f5f54-5357-4072-9a9e-a83a1b27f396

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_rectangle_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_mono
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_symm
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_tile_of_row_gap
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_tile_of_column_gap
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_sameColor_tileIndex_relation
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
theorem _root_.solution
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (component : Nat × Nat → Finset L.Site)
    (hcomponentTile : ∀ index, component index ⊆ L.tile blockWidth index)
    (hcomponentNotCorner : ∀ index site, site ∈ component index →
      ¬ L.cornerCutout blockWidth margin site)
    (parityOffset : Nat) (leftIndex rightIndex : Nat × Nat)
    (hevenLeft : Even (leftIndex.1 + leftIndex.2 + parityOffset))
    (hevenRight : Even (rightIndex.1 + rightIndex.2 + parityOffset))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range (component leftIndex) (component rightIndex) := by
  rcases sameColor_tileIndex_relation parityOffset leftIndex rightIndex hevenLeft hevenRight hne with
      hrowForward | hrowBackward | hcolumnForward | hcolumnBackward |
        hdiagonalUp | hdiagonalDown | hdiagonalLeftUp | hdiagonalLeftDown
  · exact CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_row_gap hrangeBlock leftIndex rightIndex hrowForward)
      (hcomponentTile leftIndex) (hcomponentTile rightIndex)
  · exact CoordinateRangeSeparated.symm L (CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_row_gap hrangeBlock rightIndex leftIndex hrowBackward)
      (hcomponentTile rightIndex) (hcomponentTile leftIndex))
  · exact CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_column_gap hrangeBlock leftIndex rightIndex
        hcolumnForward)
      (hcomponentTile leftIndex) (hcomponentTile rightIndex)
  · exact CoordinateRangeSeparated.symm L (CoordinateRangeSeparated.mono L
      (L.coordinateRangeSeparated_tile_of_column_gap hrangeBlock rightIndex leftIndex
        hcolumnBackward)
      (hcomponentTile rightIndex) (hcomponentTile leftIndex))
  · have hrightIndex : (leftIndex.1 + 1, leftIndex.2 + 1) = rightIndex := by
      apply Prod.ext <;> omega
    exact L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
      hblockWidth hrangeMargin leftIndex (component leftIndex) (component rightIndex)
      (hcomponentTile leftIndex)
      (fun site hsite => hcomponentNotCorner leftIndex site hsite)
      (by simpa only [hrightIndex] using hcomponentTile rightIndex)
  · have hleftIndex : (leftIndex.1, rightIndex.2 + 1) = leftIndex := by
      apply Prod.ext <;> omega
    have hrightIndex : (leftIndex.1 + 1, rightIndex.2) = rightIndex := by
      apply Prod.ext <;> omega
    exact L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
      hblockWidth hrangeMargin (leftIndex.1, rightIndex.2)
      (component leftIndex) (component rightIndex)
      (by simpa only [hleftIndex] using hcomponentTile leftIndex)
      (fun site hsite => hcomponentNotCorner leftIndex site hsite)
      (by simpa only [hrightIndex] using hcomponentTile rightIndex)
  · have hrightIndex : (rightIndex.1, leftIndex.2 + 1) = rightIndex := by
      apply Prod.ext <;> omega
    have hleftIndex : (rightIndex.1 + 1, leftIndex.2) = leftIndex := by
      apply Prod.ext <;> omega
    exact CoordinateRangeSeparated.symm L
      (L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
        hblockWidth hrangeMargin (rightIndex.1, leftIndex.2)
        (component rightIndex) (component leftIndex)
        (by simpa only [hrightIndex] using hcomponentTile rightIndex)
        (fun site hsite => hcomponentNotCorner rightIndex site hsite)
        (by simpa only [hleftIndex] using hcomponentTile leftIndex))
  · have hleftIndex : (rightIndex.1 + 1, rightIndex.2 + 1) = leftIndex := by
      apply Prod.ext <;> omega
    exact CoordinateRangeSeparated.symm L
      (L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
        hblockWidth hrangeMargin rightIndex (component rightIndex) (component leftIndex)
        (hcomponentTile rightIndex)
        (fun site hsite => hcomponentNotCorner rightIndex site hsite)
        (by simpa only [hleftIndex] using hcomponentTile leftIndex))
end QEC.Bounds.BPTSquareLattice

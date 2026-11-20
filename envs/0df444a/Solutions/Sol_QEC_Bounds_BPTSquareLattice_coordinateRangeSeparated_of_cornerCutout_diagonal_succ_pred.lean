-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:01.958835+00:00
-- url     : https://prove2.me/submissions/2f60651a-c9c2-4976-8d1e-4ebf5cc92a33

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_rectangle_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_tile
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_symm
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
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) (left right : Finset L.Site)
    (hleftTile : left ⊆ L.tile blockWidth (index.1, index.2 + 1))
    (hleftNotCorner : ∀ site ∈ left, ¬ L.cornerCutout blockWidth margin site)
    (hrightTile : right ⊆ L.tile blockWidth (index.1 + 1, index.2)) :
    L.CoordinateRangeSeparated range left right := by
  intro leftSite hleftSite rightSite hrightSite
  have hleftTileSite := hleftTile hleftSite
  have hrightTileSite := hrightTile hrightSite
  have hleftIndex : L.tileIndex blockWidth leftSite = (index.1, index.2 + 1) :=
    L.tileIndex_eq_of_mem_tile hblockWidth hleftTileSite
  have hrowIndex : leftSite.1.val / blockWidth = index.1 :=
    congrArg Prod.fst hleftIndex
  have hcolumnIndex : leftSite.2.val / blockWidth = index.2 + 1 :=
    congrArg Prod.snd hleftIndex
  have hrowDecomposition : leftSite.1.val =
      index.1 * blockWidth + leftSite.1.val % blockWidth := by
    calc
      leftSite.1.val = blockWidth * (leftSite.1.val / blockWidth) +
          leftSite.1.val % blockWidth :=
        (Nat.div_add_mod leftSite.1.val blockWidth).symm
      _ = index.1 * blockWidth + leftSite.1.val % blockWidth := by
        rw [hrowIndex, Nat.mul_comm]
  have hcolumnDecomposition : leftSite.2.val = index.2 * blockWidth + blockWidth +
      leftSite.2.val % blockWidth := by
    calc
      leftSite.2.val = blockWidth * (leftSite.2.val / blockWidth) +
          leftSite.2.val % blockWidth :=
        (Nat.div_add_mod leftSite.2.val blockWidth).symm
      _ = (index.2 + 1) * blockWidth + leftSite.2.val % blockWidth := by
        rw [hcolumnIndex, Nat.mul_comm]
      _ = index.2 * blockWidth + blockWidth + leftSite.2.val % blockWidth := by
        simp [Nat.add_mul]
  have hleftBounds := (L.mem_square_iff (index.1 * blockWidth,
    (index.2 + 1) * blockWidth) blockWidth leftSite).mp hleftTileSite
  have hrightBounds := (L.mem_square_iff ((index.1 + 1) * blockWidth,
    index.2 * blockWidth) blockWidth rightSite).mp hrightTileSite
  by_cases hrowGap : range ≤ rightSite.1.val - leftSite.1.val
  · exact Or.inr (Or.inl hrowGap)
  by_cases hcolumnGap : range ≤ leftSite.2.val - rightSite.2.val
  · exact Or.inr (Or.inr (Or.inl hcolumnGap))
  exfalso
  apply hleftNotCorner leftSite hleftSite
  have hrightRowLower : index.1 * blockWidth + blockWidth ≤ rightSite.1.val := by
    simpa [Nat.add_mul] using hrightBounds.1
  have hrightColumnUpper : rightSite.2.val < index.2 * blockWidth + blockWidth := by
    exact hrightBounds.2.2.2
  have hrowOrder : leftSite.1.val ≤ rightSite.1.val := by
    have hrowTileEdge : index.1 * blockWidth + blockWidth ≤
        (index.1 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hcolumnOrder : rightSite.2.val ≤ leftSite.2.val := by
    have hcolumnTileEdge : index.2 * blockWidth + blockWidth ≤
        (index.2 + 1) * blockWidth := by simp [Nat.add_mul]
    omega
  have hrowGapLt : rightSite.1.val - leftSite.1.val < range :=
    Nat.lt_of_not_ge hrowGap
  have hcolumnGapLt : leftSite.2.val - rightSite.2.val < range :=
    Nat.lt_of_not_ge hcolumnGap
  constructor
  · right
    omega
  · left
    omega
end QEC.Bounds.BPTSquareLattice

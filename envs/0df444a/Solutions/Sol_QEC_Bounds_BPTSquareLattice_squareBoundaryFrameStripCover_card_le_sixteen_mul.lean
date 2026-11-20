-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.squareBoundaryFrameStripCover_card_le_sixteen_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:35:56.104173+00:00
-- url     : https://prove2.me/submissions/2da8c85b-0cfd-4191-abce-bc2c734b9864

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
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width) :
    (L.squareBoundaryFrameStripCover origin width margin).card ≤ 16 * margin * width := by
  let bound := (margin + margin) * (width + margin + margin)
  have hLowerRow : (L.squareBoundaryFrameLowerRow origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameLowerRow] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 - margin)
        (margin + margin) (width + margin + margin)
  have hUpperRow : (L.squareBoundaryFrameUpperRow origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameUpperRow] using
      L.rectangle_card_le_area (origin.1 + width - margin, origin.2 - margin)
        (margin + margin) (width + margin + margin)
  have hLowerColumn : (L.squareBoundaryFrameLowerColumn origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameLowerColumn, Nat.mul_comm] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 - margin)
        (width + margin + margin) (margin + margin)
  have hUpperColumn : (L.squareBoundaryFrameUpperColumn origin width margin).card ≤ bound := by
    simpa [bound, squareBoundaryFrameUpperColumn, Nat.mul_comm] using
      L.rectangle_card_le_area (origin.1 - margin, origin.2 + width - margin)
        (width + margin + margin) (margin + margin)
  have hcoverCard : (L.squareBoundaryFrameStripCover origin width margin).card ≤
      (L.squareBoundaryFrameLowerRow origin width margin).card +
        (L.squareBoundaryFrameUpperRow origin width margin).card +
          (L.squareBoundaryFrameLowerColumn origin width margin).card +
            (L.squareBoundaryFrameUpperColumn origin width margin).card := by
    calc
      (L.squareBoundaryFrameStripCover origin width margin).card =
          (((L.squareBoundaryFrameLowerRow origin width margin ∪
            L.squareBoundaryFrameUpperRow origin width margin) ∪
              L.squareBoundaryFrameLowerColumn origin width margin) ∪
                L.squareBoundaryFrameUpperColumn origin width margin).card := rfl
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin ∪
          L.squareBoundaryFrameUpperRow origin width margin) ∪
            L.squareBoundaryFrameLowerColumn origin width margin).card +
              (L.squareBoundaryFrameUpperColumn origin width margin).card :=
        Finset.card_union_le _ _
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin ∪
          L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card) +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ ≤ ((L.squareBoundaryFrameLowerRow origin width margin).card +
          (L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card) +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by
        gcongr
        exact Finset.card_union_le _ _
      _ = (L.squareBoundaryFrameLowerRow origin width margin).card +
          (L.squareBoundaryFrameUpperRow origin width margin).card +
            (L.squareBoundaryFrameLowerColumn origin width margin).card +
              (L.squareBoundaryFrameUpperColumn origin width margin).card := by omega
  have hlinear : (L.squareBoundaryFrameStripCover origin width margin).card ≤
      bound + bound + bound + bound := by omega
  have hside : width + margin + margin ≤ width + width := by omega
  have hbound : bound ≤ (margin + margin) * (width + width) := by
    exact Nat.mul_le_mul_left _ hside
  calc
    (L.squareBoundaryFrameStripCover origin width margin).card ≤
        bound + bound + bound + bound := hlinear
    _ ≤ 4 * bound := by omega
    _ ≤ 4 * ((margin + margin) * (width + width)) := Nat.mul_le_mul_left _ hbound
    _ = 16 * margin * width := by ring
end QEC.Bounds.BPTSquareLattice

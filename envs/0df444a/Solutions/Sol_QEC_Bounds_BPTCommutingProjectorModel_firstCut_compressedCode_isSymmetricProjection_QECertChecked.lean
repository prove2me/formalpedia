-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:02:13.83217+00:00
-- url     : https://prove2.me/submissions/6c0cf955-9ae4-4179-a4a4-bccb76faa7d8

import Definitions.Def_QEC_Import_Compact_0f5a8c0e18c8f014
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutFactorNonzero
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_FirstCutCodeProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutGlobalCoordinateTransport_conj_fullCodeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutProjectorMC_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCut_overlap_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_adjoint_eq_self
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_idempotent
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_of_isometric_compression_commuting
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_product_commutes_leftIsotypicSectorLift
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_productBlockRegrouping_apply_tmul_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift_QECertChecked
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



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.firstCut_compressedCode_isSymmetricProjection_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «component»
  dsimp only
  let AB := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region)
  let H := component.1.restrictScalars Complex
  let D := M.fourFactorD region
  let J := tensorTripleSubtypeEmbedding (A := AB) (C := D) H
  let R := M.firstCutCodeLift region
  have hR : R.IsSymmetricProjection := by
    have hfull : M.fullCodeProjector.IsSymmetricProjection := by
      constructor
      · exact M.fullCodeProjector_idempotent
      · exact (LinearMap.isSymmetric_iff_isSelfAdjoint M.fullCodeProjector).mpr
          M.fullCodeProjector_adjoint_eq_self
    change (M.firstCutCodeLift region).IsSymmetricProjection
    rw [← M.firstCutGlobalCoordinateTransport_conj_fullCodeProjector region]
    exact (isSymmetricProjection_conjOperator_iff
      (M.firstCutGlobalCoordinateTransport region) M.fullCodeProjector).mpr hfull
  have hself : LinearMap.adjoint (M.firstCutProjectorMC region) = M.firstCutProjectorMC region :=
    (M.firstCutProjectorMC_isSymmetricProjection region).isSymmetric.adjoint_eq
  have hover : Commute (overlapLiftLeft (C := D) (M.firstCutProjectorMC region))
      (overlapLiftRight (A := AB) (M.fourFactorProjectorCDLocal region)) :=
    M.firstCut_overlap_commute region
  have hJJ : J.comp (LinearMap.adjoint J) = M.firstCutSectorLift region component := by
    simpa only [J, AB, H, D, firstCutSectorLift] using
      (tensorTripleSubtypeEmbedding_comp_adjoint_eq_leftIsotypicSectorLift_QECertChecked
        (M.firstCutProjectorMC region) component (C := D))
  have hcommuteSector : Commute R (M.firstCutSectorLift region component) := by
    simpa only [R, AB, D, firstCutCodeLift, firstCutSectorLift] using
      (overlap_product_commutes_leftIsotypicSectorLift
        (M.firstCutProjectorMC region) (M.fourFactorProjectorCDLocal region)
        hself hover component)
  have hcommute : Commute R (J.comp (LinearMap.adjoint J)) :=
    hJJ.symm ▸ hcommuteSector
  change ((LinearMap.adjoint J).comp (R.comp J)).IsSymmetricProjection
  exact isSymmetricProjection_of_isometric_compression_commuting
    J (LinearMap.adjoint J) R
    (adjoint_tensorTripleSubtypeEmbedding_comp_tensorTripleSubtypeEmbedding (A := AB) (C := D) H)
    rfl hR hcommute
end QEC.Bounds.BPTCommutingProjectorModel

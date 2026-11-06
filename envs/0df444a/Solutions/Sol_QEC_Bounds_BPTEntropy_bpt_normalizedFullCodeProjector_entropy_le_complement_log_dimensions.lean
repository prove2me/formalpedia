-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.bpt_normalizedFullCodeProjector_entropy_le_complement_log_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:39:08.723461+00:00
-- url     : https://prove2.me/submissions/27a90434-651d-4d10-b036-9ead98d09bfe

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_bpt_correctable_region_entropy_identity
import Theorems.Thm_QEC_Bounds_BPTEntropy_vonNeumannEntropy_abc_le_c_of_conditional_substitutions
import Theorems.Thm_QEC_Bounds_BPTEntropy_normalizedFullCodeProjector_supportedOn
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_leftMarginal_abcFactorization_eq_complementABCErasure
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_leftMarginal_bacOfAbcFactorization_eq_complementBACErasure
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_conjDensity
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_Qudit_vonNeumannEntropy_le_sum_log_registerDimensions
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
open scoped TensorProduct
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution
    {L : BPTQuditLattice} {κ : Type u} [Fintype κ]
    (M : BPTCommutingProjectorModel L κ)
    (parameter : BPTCommutingProjectorModel.EncodedQubitParameter M)
    (A B : Finset L.Site) (hdisjoint : Disjoint A B)
    (recoveryA : QuantumChannel (M.regionSubsystem A).complementSystem L.Register)
    (hcorrectA : Correctable L.Register (M.regionSubsystem A).complementSystem M.codeSpace
      (M.regionSubsystem A).erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel (M.regionSubsystem B).complementSystem L.Register)
    (hcorrectB : Correctable L.Register (M.regionSubsystem B).complementSystem M.codeSpace
      (M.regionSubsystem B).erasureChannelFromRegister recoveryB) :
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy <=
      ∑ i : (_root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem (M.regionSubsystem A)
        (M.regionSubsystem B)).ComplementCoordinates,
        Real.logb 2 (L.localDimension i : Real) := by
  let S := M.regionSubsystem A
  let T := M.regionSubsystem B
  let C := _root_.QEC.Bounds.BPTEntropy.QuditSubsystem.unionSubsystem S T
  have hST : Disjoint S.selected T.selected := by
    simpa [S, T] using hdisjoint
  let Lambda := normalizedFullCodeProjector M parameter
  let rhoABC := (QuditSubsystem.abcFactorization S T hST).conjDensity Lambda
  have hLambdaSupported : DensityOperator.SupportedOn M.codeSpace Lambda := by
    dsimp [Lambda]
    exact normalizedFullCodeProjector_supportedOn M parameter
  have hAglobal := bpt_correctable_region_entropy_identity M A recoveryA hcorrectA Lambda
    hLambdaSupported
  have hBglobal := bpt_correctable_region_entropy_identity M B recoveryB hcorrectB Lambda
    hLambdaSupported
  have hA : rhoABC.vonNeumannEntropy - (leftMarginal rhoABC).vonNeumannEntropy =
      - (rightMarginal rhoABC).vonNeumannEntropy := by
    dsimp [rhoABC]
    rw [QuditSubsystem.leftMarginal_abcFactorization_eq_complementABCErasure]
    rw [QuditSubsystem.rightMarginal_abcFactorization_eq_selectedPartialTraceFromRegister]
    rw [vonNeumannEntropy_conjDensity]
    rw [vonNeumannEntropy_conjDensity]
    exact hAglobal
  have hB : rhoABC.vonNeumannEntropy -
      (leftMarginal ((abcToBac S.selectedSystem T.selectedSystem C.complementSystem).conjDensity rhoABC)).vonNeumannEntropy =
      - (rightMarginal ((abcToBac S.selectedSystem T.selectedSystem C.complementSystem).conjDensity rhoABC)).vonNeumannEntropy := by
    dsimp [rhoABC]
    rw [QuditSubsystem.leftMarginal_bacOfAbcFactorization_eq_complementBACErasure]
    rw [QuditSubsystem.rightMarginal_bacOfAbcFactorization_eq_selectedPartialTraceFromRegister]
    rw [vonNeumannEntropy_conjDensity, vonNeumannEntropy_conjDensity]
    exact hBglobal
  have hABC : rhoABC.vonNeumannEntropy <=
      (leftMarginal (leftMarginal rhoABC)).vonNeumannEntropy :=
    vonNeumannEntropy_abc_le_c_of_conditional_substitutions S.selectedSystem T.selectedSystem
      C.complementSystem rhoABC hA hB
  have hC := Qudit.vonNeumannEntropy_le_sum_log_registerDimensions C.complementDimensions
    (leftMarginal (leftMarginal rhoABC))
  calc
    (normalizedFullCodeProjector M parameter).vonNeumannEntropy = Lambda.vonNeumannEntropy := by
      rfl
    _ = rhoABC.vonNeumannEntropy := by
      dsimp [rhoABC]
      rw [vonNeumannEntropy_conjDensity]
    _ <= (leftMarginal (leftMarginal rhoABC)).vonNeumannEntropy := hABC
    _ <= ∑ i : C.ComplementCoordinates, Real.logb 2 (L.localDimension i : Real) := hC
end QEC.Bounds.BPTEntropy

-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.erasure_correctable_entropy_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:54.580216+00:00
-- url     : https://prove2.me/submissions/ad41ef6e-c5d5-4b31-b2ae-d932eb7c6794

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_conjDensity_pureDensity
import Theorems.Thm_QEC_Bounds_BPTEntropy_selectedReferenceMarginal_eq_rightMarginal_transport
import Theorems.Thm_QEC_Bounds_BPTEntropy_leftMarginal_selectedReferenceTransport_eq_erasure
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_leftMarginal_spectralPurification_eq
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification
import Theorems.Thm_QEC_Semantics_DensityOperator_rightMarginal_spectralPurification_eq
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure
import Theorems.Thm_QEC_Semantics_DensityOperator_vonNeumannEntropy_tensorDensity
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_selectedReferenceMarginal_factorizes
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
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
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho) :
    rho.vonNeumannEntropy -
        (S.erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
      - (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy := by
  let purification : DensityOperator.FinitePurification rho (Qudit.QuditRegister q) :=
    { vector := rho.spectralPurificationVector
      normSq_one := rho.spectralPurificationVector_normSq
      rightMarginal_eq := rho.rightMarginal_spectralPurification }
  have hfactor := S.erasureRecovery_implies_selectedReferenceMarginal_factorizes
    C recovery hcorrect rho hsupported (Qudit.QuditRegister q) purification
  let U := S.selectedReferenceTransport (Qudit.QuditRegister q)
  let psi := U rho.spectralPurificationVector
  have hpsi : ‖psi‖ ^ 2 = 1 := by
    change ‖U.toLinearIsometryEquiv rho.spectralPurificationVector‖ ^ 2 = 1
    rw [U.toLinearIsometryEquiv.norm_map]
    exact rho.spectralPurificationVector_normSq
  have hpure : U.conjDensity (spectralPurification rho) = pureDensity psi hpsi := by
    simpa [U, psi, spectralPurification] using
      conjDensity_pureDensity U rho.spectralPurificationVector
        rho.spectralPurificationVector_normSq
  have hfactorized :
      rightMarginal (U.conjDensity (spectralPurification rho)) =
        tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
          (leftMarginal (spectralPurification rho)) := by
    calc
      rightMarginal (U.conjDensity (spectralPurification rho)) =
          S.selectedReferenceMarginal (Qudit.QuditRegister q) (spectralPurification rho) := by
            exact (selectedReferenceMarginal_eq_rightMarginal_transport S
              (Qudit.QuditRegister q) (spectralPurification rho)).symm
      _ = tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
          (leftMarginal (spectralPurification rho)) := by
            simpa [purification, spectralPurification] using hfactor
  have hright_left :
      (rightMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy =
        (leftMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy := by
    rw [hpure]
    exact vonNeumannEntropy_rightMarginal_eq_leftMarginal_pure psi hpsi
  have hleft_erasure :
      leftMarginal (U.conjDensity (spectralPurification rho)) =
        S.erasureChannelFromRegister.mapDensity rho := by
    rw [leftMarginal_selectedReferenceTransport_eq_erasure S (Qudit.QuditRegister q)
      (spectralPurification rho), rho.rightMarginal_spectralPurification_eq]
  have hfactor_entropy :
      (rightMarginal (U.conjDensity (spectralPurification rho))).vonNeumannEntropy =
        (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy +
          (leftMarginal (spectralPurification rho)).vonNeumannEntropy := by
    rw [hfactorized, vonNeumannEntropy_tensorDensity]
  have herasure_entropy :
      (S.erasureChannelFromRegister.mapDensity rho).vonNeumannEntropy =
        (S.selectedPartialTraceFromRegister.mapDensity rho).vonNeumannEntropy +
      rho.vonNeumannEntropy := by
    rw [← hleft_erasure, ← hright_left, hfactor_entropy,
      rho.leftMarginal_spectralPurification_eq]
  linarith
end QEC.Bounds.BPTEntropy

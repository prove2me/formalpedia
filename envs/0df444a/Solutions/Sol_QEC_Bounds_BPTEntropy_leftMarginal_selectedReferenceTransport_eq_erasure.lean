-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.leftMarginal_selectedReferenceTransport_eq_erasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:10:52.842822+00:00
-- url     : https://prove2.me/submissions/8d3993ad-475d-405c-ae63-b05ac1276568

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_tensorDensity_toOperator
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_log2Matrix_apply
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_logMatrix_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_complementCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_card_selectedCoordinates
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_apply_localEmbedding
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_localEmbedding_apply
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_registerFactorization_apply_basis
import Theorems.Thm_QEC_Semantics_FiniteSubsystem_selectedPartialTrace_toLinearMap
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_conjOperator_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_linearMap_ext_of_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorization_apply_basis
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
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : QuditSubsystem q) (Ref : Type u)
    [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref] [FiniteQuantumSystem Ref]
    (omega : DensityOperator (CompositeSystem (Qudit.QuditRegister q) Ref)) :
    leftMarginal ((S.selectedReferenceTransport Ref).conjDensity omega) =
      S.erasureChannelFromRegister.mapDensity (rightMarginal omega) := by
  apply DensityOperator.ext_toOperator
  let bGlobal := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let bRef := stdOrthonormalBasis Complex Ref
  let basis := bGlobal.tensorProduct bRef
  let Phi : Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator S.complementSystem :=
    S.erasureChannelFromRegister.toLinearMap.comp
      (partialTraceRightRaw (Qudit.QuditRegister q) Ref)
  let Psi : Operator (CompositeSystem (Qudit.QuditRegister q) Ref) →ₗ[Complex]
      Operator S.complementSystem :=
    (partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)).comp
      ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperatorLinearMap.comp
        (S.selectedReferenceTransport Ref).conjOperatorLinearMap)
  have hmaps : Phi = Psi := by
    apply QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    rintro ⟨x, r⟩ ⟨y, s⟩
    simp only [Phi, Psi, LinearMap.comp_apply, basis,
      OrthonormalBasis.tensorProduct_apply']
    change S.erasureChannelFromRegister
        (partialTraceRightRaw (Qudit.QuditRegister q) Ref
          (InnerProductSpace.rankOne Complex
            ((bGlobal x) ⊗ₜ[Complex] (bRef r))
            ((bGlobal y) ⊗ₜ[Complex] (bRef s))).toLinearMap) =
      partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)
        ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperator
          ((S.selectedReferenceTransport Ref).conjOperator
            (InnerProductSpace.rankOne Complex
              ((bGlobal x) ⊗ₜ[Complex] (bRef r))
              ((bGlobal y) ⊗ₜ[Complex] (bRef s))).toLinearMap))
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    simp only [map_smul]
    rw [S.erasureChannelFromRegister_rankOne_basis]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [S.selectedReferenceTransport_apply_tmul]
    dsimp only [bGlobal]
    rw [S.registerFactorization_apply_basis x, S.registerFactorization_apply_basis y]
    simp only [S.selectedReferenceReordering_apply_tmul]
    rw [QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [TensorProduct.inner_tmul]
    simp [smul_smul, mul_comm]
  change partialTraceRightRaw S.complementSystem (CompositeSystem S.selectedSystem Ref)
      ((tensorSwap (CompositeSystem S.selectedSystem Ref) S.complementSystem).conjOperator
        ((S.selectedReferenceTransport Ref).conjOperator omega.toOperator)) =
    S.erasureChannelFromRegister
      (partialTraceRightRaw (Qudit.QuditRegister q) Ref omega.toOperator)
  exact (LinearMap.congr_fun hmaps omega.toOperator).symm
end QEC.Bounds.BPTEntropy

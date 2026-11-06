-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.right_factor_isSymmetricProjection_of_rankOne_tensor_projection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:06:32.656552+00:00
-- url     : https://prove2.me/submissions/4242f062-7e8d-46b5-b59a-881555ee90bd

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_right_factor_idempotent_of_tensor_product_projection
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
theorem _root_.solution
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (phi : H) (hphi : ‖phi‖ = 1) (Q : Semantics.Operator K)
    (hprojection :
      LinearMap.IsSymmetricProjection
        (TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)) :
    LinearMap.IsSymmetricProjection Q := by
  let P : Semantics.Operator H := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hP : P.IsSymmetricProjection := by
    simpa [P] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hphi)
  have hphi0 : phi ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hphi
    norm_num at hphi
  have hP0 : P ≠ 0 := by
    intro hzero
    have happly := congrArg (fun operator => operator phi) hzero
    have hinner : inner Complex phi phi = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
    change inner Complex phi phi • phi = 0 at happly
    rw [hinner, one_smul] at happly
    exact hphi0 happly
  have hidempotent : Q * Q = Q := by
    exact right_factor_idempotent_of_tensor_product_projection P Q
      hP.isIdempotentElem hP0 (by simpa [P] using hprojection)
  have hselfTensor :
      LinearMap.adjoint (TensorProduct.map P Q) = TensorProduct.map P Q :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint _).mp hprojection.isSymmetric
  have hself : LinearMap.adjoint Q = Q := by
    apply LinearMap.ext
    intro vector
    have hmap : TensorProduct.map P (LinearMap.adjoint Q) = TensorProduct.map P Q := by
      calc
        TensorProduct.map P (LinearMap.adjoint Q) =
            LinearMap.adjoint (TensorProduct.map P Q) := by
              rw [TensorProduct.adjoint_map, hP.isSymmetric.adjoint_eq]
        _ = TensorProduct.map P Q := hselfTensor
    have happly := congrArg (fun operator => operator (phi ⊗ₜ[Complex] vector)) hmap
    have hinner : inner Complex phi phi = 1 := by
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
    have htensor : phi ⊗ₜ[Complex] (LinearMap.adjoint Q) vector =
        phi ⊗ₜ[Complex] Q vector := by
      simpa [P, InnerProductSpace.rankOne_apply, hinner, hphi] using happly
    apply ext_inner_left Complex
    intro test
    have hinnerTensor := congrArg
      (fun tensor => inner Complex (phi ⊗ₜ[Complex] test) tensor) htensor
    simpa only [TensorProduct.inner_tmul, hinner, one_mul] using hinnerTensor
  constructor
  · exact hidempotent
  · exact (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr hself
end QEC.Bounds.BPTCommutingProjectorModel

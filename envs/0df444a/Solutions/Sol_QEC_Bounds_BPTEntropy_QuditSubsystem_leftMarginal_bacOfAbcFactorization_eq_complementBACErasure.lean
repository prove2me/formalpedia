-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.QuditSubsystem.leftMarginal_bacOfAbcFactorization_eq_complementBACErasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:36:00.89713+00:00
-- url     : https://prove2.me/submissions/292728f8-40d0-4719-a32d-16abde48b634

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_abcFactorization_apply_basis
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_complementBACFactorization_apply_basis
import Theorems.Thm_QEC_Bounds_BPTEntropy_QuditSubsystem_splitComplementBACLabel_splitLabel
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
open QEC.Bounds.BPTEntropy.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι -> Nat}
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTEntropy.QuditSubsystem
theorem _root_.solution
    (S T : QuditSubsystem q) (hST : Disjoint S.selected T.selected)
    (rho : DensityOperator (Qudit.QuditRegister q)) :
    leftMarginal ((abcToBac S.selectedSystem T.selectedSystem
      (unionSubsystem S T).complementSystem).conjDensity
        ((abcFactorization S T hST).conjDensity rho)) =
      (complementBACFactorization S T hST).conjDensity
        (T.erasureChannelFromRegister.mapDensity rho) := by
  apply DensityOperator.ext_toOperator
  let basis := EuclideanSpace.basisFun (Qudit.Label q) Complex
  let AC := CompositeSystem S.selectedSystem (unionSubsystem S T).complementSystem
  let Phi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator AC :=
    (partialTraceRightRaw AC T.selectedSystem).comp
      ((tensorSwap T.selectedSystem AC).conjOperatorLinearMap.comp
        ((abcToBac S.selectedSystem T.selectedSystem
          (unionSubsystem S T).complementSystem).conjOperatorLinearMap.comp
          (abcFactorization S T hST).conjOperatorLinearMap))
  let Psi : Operator (Qudit.QuditRegister q) →ₗ[Complex] Operator AC :=
    (complementBACFactorization S T hST).conjOperatorLinearMap.comp
      T.erasureChannelFromRegister.toLinearMap
  have hmaps : Phi = Psi := by
    apply Semantics.QuditSubsystem.linearMap_ext_of_rankOne_basis basis Phi Psi
    intro x y
    simp only [Phi, Psi, LinearMap.comp_apply]
    change partialTraceRightRaw AC T.selectedSystem
        ((tensorSwap T.selectedSystem AC).conjOperator
          ((abcToBac S.selectedSystem T.selectedSystem
            (unionSubsystem S T).complementSystem).conjOperator
            ((abcFactorization S T hST).conjOperator
              (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap))) =
      (complementBACFactorization S T hST).conjOperator
        (T.erasureChannelFromRegister
          (InnerProductSpace.rankOne Complex (basis x) (basis y)).toLinearMap)
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    rw [abcFactorization_apply_basis S T hST x, abcFactorization_apply_basis S T hST y]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [abcToBac_apply_tmul]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    simp only [tensorSwap_apply_tmul]
    rw [Semantics.QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
    rw [T.erasureChannelFromRegister_rankOne_basis x y]
    change _ = (complementBACFactorization S T hST).conjOperatorLinearMap
      (inner Complex
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
          (T.splitLabel y).1)
        (EuclideanSpace.basisFun (Qudit.Label T.selectedDimensions) Complex
          (T.splitLabel x).1) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (T.splitLabel x).2)
          (EuclideanSpace.basisFun (Qudit.Label T.complementDimensions) Complex
            (T.splitLabel y).2)).toLinearMap)
    rw [map_smul]
    rw [UnitaryTransport.conjOperatorLinearMap_apply]
    rw [Semantics.QuditSubsystem.conjOperator_rankOne]
    have hcomp_x := complementBACFactorization_apply_basis S T hST (T.splitLabel x).2
    have hcomp_y := complementBACFactorization_apply_basis S T hST (T.splitLabel y).2
    rw [hcomp_x, hcomp_y]
    rw [splitComplementBACLabel_splitLabel, splitComplementBACLabel_splitLabel]
    rfl
  exact LinearMap.congr_fun hmaps rho.toOperator
end QEC.Bounds.BPTEntropy.QuditSubsystem

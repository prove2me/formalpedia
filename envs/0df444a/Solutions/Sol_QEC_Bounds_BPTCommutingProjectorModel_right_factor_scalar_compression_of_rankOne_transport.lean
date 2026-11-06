-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.right_factor_scalar_compression_of_rankOne_transport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:58:42.3012+00:00
-- url     : https://prove2.me/submissions/6bdffb1b-e22b-4f71-b72d-a3689e4eec43

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RightProjection
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_RankOneTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tmul_right_eq_of_tmul_left_eq_of_ne_zero
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
open scoped ComplexOrder TensorProduct
universe u
open QEC.Bounds.BPTCommutingProjectorModel
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {H A B : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B]
    (T : Semantics.UnitaryTransport H (Semantics.CompositeSystem A B))
    (R L : Semantics.Operator H) (phi : A) (hphi : ‖phi‖ = 1)
    (Q X : Semantics.Operator B) (scalar : Complex)
    (hR : T.conjOperator R =
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q)
    (hL : T.conjOperator L =
      TensorProduct.map (1 : Semantics.Operator A) X)
    (hscalar : R * L * R = scalar • R) :
    Q * X * Q = scalar • Q := by
  have hinner : inner Complex phi phi = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    simpa [hphi]
  have hphi0 : phi ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hphi
    norm_num at hphi
  have htransported :
      TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q *
          TensorProduct.map (1 : Semantics.Operator A) X *
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q =
        scalar •
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q := by
    calc
      _ = T.conjOperator R * T.conjOperator L * T.conjOperator R := by
        rw [hR, hL]
      _ = T.conjOperator (R * L * R) := by
        rw [Semantics.UnitaryTransport.conjOperator_mul,
          Semantics.UnitaryTransport.conjOperator_mul]
      _ = T.conjOperator (scalar • R) := congrArg T.conjOperator hscalar
      _ = scalar • T.conjOperator R :=
        T.conjOperatorLinearMap.map_smul scalar R
      _ = scalar •
          TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap Q := by
        rw [hR]
  apply LinearMap.ext
  intro vector
  apply tmul_right_eq_of_tmul_left_eq_of_ne_zero phi hphi0
  have happly := congrArg
    (fun operator => operator (phi ⊗ₜ[Complex] vector)) htransported
  simpa [InnerProductSpace.rankOne_apply, hinner, hphi, TensorProduct.map_tmul,
    LinearMap.smul_apply] using happly
end QEC.Bounds.BPTCommutingProjectorModel

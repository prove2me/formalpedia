-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.finrank_range_le_one_of_two_factor_scalar_compressions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:36:37.923209+00:00
-- url     : https://prove2.me/submissions/31515d6c-9dbf-4445-9cc0-6144903a7048

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_linearMap_eq_zero_of_cross_and_equal_gram
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_eq_zero_of_rightAmplitude_eq_zero
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_orthonormal_pair_fixed_of_one_lt_range_finrank
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
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem N C))
    (hP : P.IsSymmetricProjection)
    (hleft : ∀ X : Semantics.Operator N, ∃ scalar : Complex,
      P * TensorProduct.map X (1 : Semantics.Operator C) * P = scalar • P)
    (hright : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P) :
    Module.finrank Complex (LinearMap.range P) ≤ 1 := by
  by_contra hle
  have hdim : 1 < Module.finrank Complex (LinearMap.range P) := Nat.lt_of_not_ge hle
  rcases exists_orthonormal_pair_fixed_of_one_lt_range_finrank P hP hdim with
    ⟨x, y, hx, hy, hxx, hyy, hnormx, hnormy, hyx⟩
  let bN := stdOrthonormalBasis Complex N
  let bC := stdOrthonormalBasis Complex C
  let A := Semantics.DensityOperator.rightAmplitude bC x
  let B := Semantics.DensityOperator.rightAmplitude bC y
  have hrawCross : Semantics.partialTraceRightRaw N C
      (InnerProductSpace.rankOne Complex x y).toLinearMap = 0 := by
    calc
      Semantics.partialTraceRightRaw N C
          (InnerProductSpace.rankOne Complex x y).toLinearMap =
          (inner Complex y x) • Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap :=
        partialTraceRightRaw_rankOne_eq_inner_smul_of_left_scalar_compression
          P hP hleft x y hx hy hxx
      _ = 0 := by rw [hyx, zero_smul]
  have hcross : A.comp (LinearMap.adjoint B) = 0 := by
    calc
      A.comp (LinearMap.adjoint B) =
          Semantics.partialTraceRightRaw N C
            (InnerProductSpace.rankOne Complex x y).toLinearMap := by
              symm
              exact partialTraceRightRaw_rankOne_eq_rightAmplitude_comp_adjoint bC x y
      _ = 0 := hrawCross
  have hrawDiag := partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
    P hP hright x y hx hy hxx hyy
  have hgram : (LinearMap.adjoint A).comp A = (LinearMap.adjoint B).comp B := by
    simpa [A, B] using adjoint_comp_eq_of_partialTraceLeftRaw_rankOne_self_eq
      bN bC x y hnormx hnormy hrawDiag
  have hAzero : A = 0 := linearMap_eq_zero_of_cross_and_equal_gram A B hcross hgram
  have hxzero : x = 0 := eq_zero_of_rightAmplitude_eq_zero bC x (by simpa [A] using hAzero)
  have hzero_one : (0 : Complex) = 1 := by simpa [hxzero] using hxx
  norm_num at hzero_one
end QEC.Bounds.BPTCommutingProjectorModel

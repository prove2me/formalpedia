-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.partialTraceLeftRaw_rankOne_self_eq_of_right_scalar_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:29:48.228835+00:00
-- url     : https://prove2.me/submissions/d8685b90-d52d-44ba-be5e-bde9073234c8

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
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
import Theorems.Thm_QEC_Semantics_FiniteMatrixEntropy_partialTraceLeftRaw_trace_pairing
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_rankOne
import Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_rankOne_comp
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
    (hscalar : ∀ Y : Semantics.Operator C, ∃ scalar : Complex,
      P * TensorProduct.map (1 : Semantics.Operator N) Y * P = scalar • P)
    (x y : Semantics.CompositeSystem N C)
    (hx : P x = x) (hy : P y = y)
    (hnormx : inner Complex x x = 1) (hnormy : inner Complex y y = 1) :
    Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
      (InnerProductSpace.rankOne Complex x x).toLinearMap =
      Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
        (InnerProductSpace.rankOne Complex y y).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply ext_inner_left Complex
  intro u
  let Y : Semantics.Operator C := (InnerProductSpace.rankOne Complex v u).toLinearMap
  let E : Semantics.Operator (Semantics.CompositeSystem N C) :=
    TensorProduct.map (1 : Semantics.Operator N) Y
  rcases hscalar Y with ⟨scalar, hcompression⟩
  have hself : LinearMap.adjoint P = P :=
    (LinearMap.isSymmetric_iff_isSelfAdjoint P).mp hP.isSymmetric
  have hmatrix (z : Semantics.CompositeSystem N C) (hz : P z = z) :
      inner Complex z (E z) = scalar * inner Complex z z := by
    calc
      inner Complex z (E z) = inner Complex (P z) (E (P z)) := by rw [hz]
      _ = inner Complex z (P (E (P z))) := by
        rw [← LinearMap.adjoint_inner_right P z (E (P z)), hself]
      _ = inner Complex z ((P * E * P) z) := by rfl
      _ = inner Complex z ((scalar • P) z) := by rw [hcompression]
      _ = scalar * inner Complex z z := by rw [LinearMap.smul_apply, hz, inner_smul_right]
  have htrace (z : Semantics.CompositeSystem N C) :
      LinearMap.trace Complex C
        ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex z z).toLinearMap).comp Y) =
        inner Complex z (E z) := by
    calc
      LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex z z).toLinearMap).comp Y) =
          LinearMap.trace Complex (Semantics.CompositeSystem N C)
            ((InnerProductSpace.rankOne Complex z z).toLinearMap.comp E) := by
              exact Semantics.FiniteMatrixEntropy.partialTraceLeftRaw_trace_pairing
                  (InnerProductSpace.rankOne Complex z z).toLinearMap Y
      _ = inner Complex z (E z) :=
        Semantics.QuditSubsystem.trace_rankOne_comp E z z
  calc
    inner Complex u
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex x x).toLinearMap v) =
        LinearMap.trace Complex C
          ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
            (InnerProductSpace.rankOne Complex x x).toLinearMap).comp Y) := by
              simpa [Y] using
                (Semantics.QuditSubsystem.trace_comp_rankOne
                  (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                    (InnerProductSpace.rankOne Complex x x).toLinearMap) v u).symm
    _ = inner Complex x (E x) := htrace x
    _ = scalar := by rw [hmatrix x hx, hnormx, mul_one]
    _ = inner Complex y (E y) := by rw [hmatrix y hy, hnormy, mul_one]
    _ = LinearMap.trace Complex C
        ((Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex y y).toLinearMap).comp Y) := (htrace y).symm
    _ = inner Complex u
        (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
          (InnerProductSpace.rankOne Complex y y).toLinearMap v) := by
            simpa [Y] using
              Semantics.QuditSubsystem.trace_comp_rankOne
                (Semantics.FiniteMatrixEntropy.partialTraceLeftRaw N C
                  (InnerProductSpace.rankOne Complex y y).toLinearMap) v u
end QEC.Bounds.BPTCommutingProjectorModel

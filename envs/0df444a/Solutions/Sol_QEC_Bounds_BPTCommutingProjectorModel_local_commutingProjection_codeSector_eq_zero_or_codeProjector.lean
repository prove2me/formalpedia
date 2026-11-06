-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.local_commutingProjection_codeSector_eq_zero_or_codeProjector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:24:37.535547+00:00
-- url     : https://prove2.me/submissions/c0101209-2375-4b83-ae4c-1aa657b84297

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_mul_of_commute
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
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
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_idempotent
import Theorems.Thm_QEC_Semantics_QuantumCode_projector_isSymmetric
import Theorems.Thm_QEC_Semantics_Qubit_localXSupport_apply
import Theorems.Thm_QEC_Semantics_Qubit_localZSupport_apply
import Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
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
    (S : Semantics.QuditSubsystem L.localDimension) (C : Semantics.QuantumCode L.Register)
    {Z : Semantics.Operator L.Register}
    (hInformation : Semantics.QuditSubsystem.NoInformationOn C S)
    (hLocal : S.OperatorSupportedOnRegister Z)
    (hProjection : Z.IsSymmetricProjection)
    (hCommute : Commute C.projector Z) :
    C.projector * Z = 0 ∨ C.projector * Z = C.projector := by
  rcases hLocal with ⟨localZ, hlocalZ⟩
  have hAll := (S.noInformationOn_iff_allLocalScalarCompression C).mp hInformation
  rcases hAll localZ with ⟨scalar, hscalar⟩
  have hProjector : C.projector.IsSymmetricProjection := by
    constructor
    · exact C.projector_idempotent
    · exact C.projector_isSymmetric
  have hsectorScalar : C.projector * Z = scalar • C.projector := by
    calc
      C.projector * Z = (C.projector * C.projector) * Z := by
        rw [show C.projector * C.projector = C.projector by
          simpa [Module.End.mul_eq_comp] using C.projector_idempotent]
      _ = C.projector * (C.projector * Z) := by rw [mul_assoc]
      _ = C.projector * (Z * C.projector) := by rw [hCommute.eq]
      _ = C.projector.comp (Z.comp C.projector) := rfl
      _ = C.projector.comp ((S.extendLocalToRegister localZ).comp C.projector) := by
        rw [hlocalZ]
      _ = scalar • C.projector := hscalar
  have hsectorProjection : (C.projector * Z).IsSymmetricProjection :=
    isSymmetricProjection_mul_of_commute hProjector hProjection hCommute
  by_cases hcode : C.projector = 0
  · left
    rw [hcode, zero_mul]
  · have hsectorIdem : (C.projector * Z) * (C.projector * Z) = C.projector * Z :=
      hsectorProjection.isIdempotentElem
    have hscalarIdem : scalar * scalar = scalar := by
      apply smul_left_injective Complex hcode
      calc
        (scalar * scalar) • C.projector =
            (scalar • C.projector) * (scalar • C.projector) := by
              rw [smul_mul_smul,
                show C.projector * C.projector = C.projector by
                  simpa [Module.End.mul_eq_comp] using C.projector_idempotent]
        _ = (C.projector * Z) * (C.projector * Z) := by rw [hsectorScalar]
        _ = C.projector * Z := hsectorIdem
        _ = scalar • C.projector := hsectorScalar
    have hfactor : scalar * (scalar - 1) = 0 := by
      calc
        scalar * (scalar - 1) = scalar * scalar - scalar := by ring
        _ = 0 := sub_eq_zero.mpr hscalarIdem
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · left
      rw [hsectorScalar, hzero, zero_smul]
    · right
      rw [hsectorScalar, sub_eq_zero.mp hone, one_smul]
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_named_isometric_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:06:44.276144+00:00
-- url     : https://prove2.me/submissions/9ad21ec6-f3a5-49b6-aef0-536e73606729

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compressed_scalar_of_two_sided_intertwining
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
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Rsub Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp (Rsub.comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    Rsub * Lsub * Rsub = scalar • Rsub := by
  let Jadj := LinearMap.adjoint J
  have hreconstruct' : R = J.comp (Rsub.comp Jadj) := hreconstruct
  have hRleft : Jadj.comp R = Rsub.comp Jadj := by
    calc
      Jadj.comp R = Jadj.comp (J.comp (Rsub.comp Jadj)) := by rw [hreconstruct']
      _ = (Jadj.comp J).comp (Rsub.comp Jadj) := by rw [← LinearMap.comp_assoc]
      _ = Rsub.comp Jadj := by rw [hJadj]; rfl
  have hRright : R.comp J = J.comp Rsub := by
    calc
      R.comp J = (J.comp (Rsub.comp Jadj)).comp J := by rw [hreconstruct']
      _ = J.comp (Rsub.comp (Jadj.comp J)) := by simp only [LinearMap.comp_assoc]
      _ = J.comp (Rsub.comp (1 : Semantics.Operator H)) := by rw [hJadj]
      _ = J.comp Rsub := by rfl
  have hRsub : Rsub = Jadj.comp (R.comp J) := by
    symm
    calc
      Jadj.comp (R.comp J) = (Jadj.comp R).comp J := by rw [← LinearMap.comp_assoc]
      _ = (Rsub.comp Jadj).comp J := by rw [hRleft]
      _ = Rsub.comp (Jadj.comp J) := by rw [LinearMap.comp_assoc]
      _ = Rsub.comp (1 : Semantics.Operator H) := by rw [hJadj]
      _ = Rsub := by rfl
  exact compressed_scalar_of_two_sided_intertwining
    J Jadj R L Rsub Lsub scalar hRleft hRright hprobe hRsub hscalar
end QEC.Bounds.BPTCommutingProjectorModel

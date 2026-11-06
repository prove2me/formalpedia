-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.conjOperator_compression_of_intertwining
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:33:55.155684+00:00
-- url     : https://prove2.me/submissions/7ead1120-9849-4ece-b2a3-a7a6969dc69e

import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_Core
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingLeft_apply_tmul
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_jointBCSectorEmbeddingRight_apply_tmul
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


attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingLeft_apply_tmul
attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorEmbeddingRight_apply_tmul

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
    {S H : Type u} [NormedAddCommGroup S] [InnerProductSpace Complex S]
    [Semantics.FiniteQuantumSystem S] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : S →ₗ[Complex] H)
    (F : Semantics.UnitaryTransport H H) (W : Semantics.UnitaryTransport S S)
    (hintertwines : F.toLinearEquiv.toLinearMap.comp J = J.comp W.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint J).comp ((F.conjOperator P).comp J) =
      W.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
  have hintertwines_apply (x : S) : F (J x) = J (W x) := by
    exact congrArg (fun f => f x) hintertwines
  have hsymm : F.symm.toLinearEquiv.toLinearMap.comp J =
      J.comp W.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro x
    have h := congrArg (fun y => F.symm y) (hintertwines_apply (W.symm x))
    simpa using h.symm
  have hFsymmAdj : LinearMap.adjoint F.symm.toLinearEquiv.toLinearMap =
      F.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact F.adjoint_symm_toLinearMap
  have hWsymmAdj : LinearMap.adjoint W.symm.toLinearEquiv.toLinearMap =
      W.toLinearEquiv.toLinearMap := by
    rw [Semantics.UnitaryTransport.symm_toLinearEquiv]
    exact W.adjoint_symm_toLinearMap
  have hleft := congrArg LinearMap.adjoint hsymm
  rw [LinearMap.adjoint_comp, hFsymmAdj, LinearMap.adjoint_comp, hWsymmAdj] at hleft
  calc
    (LinearMap.adjoint J).comp ((F.conjOperator P).comp J) =
        ((LinearMap.adjoint J).comp F.toLinearEquiv.toLinearMap).comp
          (P.comp (F.symm.toLinearEquiv.toLinearMap.comp J)) := by
          simp only [Semantics.UnitaryTransport.conjOperator,
            Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]
    _ = (W.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint J)).comp
          (P.comp (J.comp W.symm.toLinearEquiv.toLinearMap)) := by
          rw [hleft, hsymm]
    _ = W.conjOperator ((LinearMap.adjoint J).comp (P.comp J)) := by
          simp only [Semantics.UnitaryTransport.conjOperator,
            Semantics.UnitaryTransport.symm_toLinearEquiv, LinearMap.comp_assoc]
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.jointBCSectorCompression_conj_tensorAssociator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:39:34.76019+00:00
-- url     : https://prove2.me/submissions/dee6738f-7c63-4504-9cff-1158c29b7869

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Compression_Transport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft
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
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A B C D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (pB : Submodule Complex B) (pC : Submodule Complex C)
    (T : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem (Semantics.CompositeSystem A B) C) D)) :
    let U := tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D
    let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
    let Jleft := jointBCSectorEmbeddingLeft pB pC
    let Jright := jointBCSectorEmbeddingRight pB pC
    (LinearMap.adjoint Jright).comp ((U.conjOperator T).comp Jright) =
      V.conjOperator ((LinearMap.adjoint Jleft).comp (T.comp Jleft)) := by
  dsimp
  let U := tensorAssociatorUnitary (Semantics.CompositeSystem A B) C D
  let V := tensorAssociatorUnitary (Semantics.CompositeSystem A pB) pC D
  let Jleft := jointBCSectorEmbeddingLeft (A := A) (D := D) pB pC
  let Jright := jointBCSectorEmbeddingRight (A := A) (D := D) pB pC
  have hUV : U.toLinearEquiv.toLinearMap.comp Jleft =
      Jright.comp V.toLinearEquiv.toLinearMap := by
    simpa [U, V, Jleft, Jright] using
      tensorAssociatorUnitary_comp_jointBCSectorEmbeddingLeft (A := A) pB pC
  have hleft : U.symm.toLinearEquiv.toLinearMap.comp Jright =
      Jleft.comp V.symm.toLinearEquiv.toLinearMap := by
    apply LinearMap.ext
    intro vector
    calc
      U.symm.toLinearEquiv.toLinearMap (Jright vector) =
          U.symm.toLinearEquiv.toLinearMap
            (U.toLinearEquiv.toLinearMap
              (Jleft (V.symm.toLinearEquiv.toLinearMap vector))) := by
        have happly := congrArg (fun map => map (V.symm.toLinearEquiv.toLinearMap vector)) hUV
        simpa [LinearMap.comp_apply] using congrArg U.symm.toLinearEquiv.toLinearMap happly.symm
      _ = Jleft (V.symm.toLinearEquiv.toLinearMap vector) := by simp
  have hleft' : U.toLinearEquiv.symm.toLinearMap.comp Jright =
      Jleft.comp V.toLinearEquiv.symm.toLinearMap := by
    simpa only [← Semantics.UnitaryTransport.symm_toLinearEquiv] using hleft
  have hUadj : LinearMap.adjoint U.symm.toLinearEquiv.toLinearMap = U.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap U.symm)
  have hVadj : LinearMap.adjoint V.symm.toLinearEquiv.toLinearMap = V.toLinearEquiv.toLinearMap := by
    simpa [Semantics.UnitaryTransport.symm_toLinearEquiv] using
      (Semantics.UnitaryTransport.adjoint_toLinearMap V.symm)
  have hright : (LinearMap.adjoint Jright).comp U.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint Jleft) := by
    have hadj := congrArg LinearMap.adjoint hleft
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hUadj, hVadj] at hadj
    exact hadj
  unfold Semantics.UnitaryTransport.conjOperator
  change (LinearMap.adjoint Jright).comp
      ((U.toLinearEquiv.toLinearMap.comp
        (T.comp U.toLinearEquiv.symm.toLinearMap)).comp Jright) =
      V.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint Jleft).comp (T.comp Jleft)).comp
          V.toLinearEquiv.symm.toLinearMap)
  calc
    (LinearMap.adjoint Jright).comp
        ((U.toLinearEquiv.toLinearMap.comp
          (T.comp U.toLinearEquiv.symm.toLinearMap)).comp Jright) =
        ((LinearMap.adjoint Jright).comp U.toLinearEquiv.toLinearMap).comp
          (T.comp (U.toLinearEquiv.symm.toLinearMap.comp Jright)) := by
      simp only [LinearMap.comp_assoc]
    _ = (V.toLinearEquiv.toLinearMap.comp (LinearMap.adjoint Jleft)).comp
          (T.comp (Jleft.comp V.toLinearEquiv.symm.toLinearMap)) := by
      rw [hright, hleft']
    _ = V.toLinearEquiv.toLinearMap.comp
        (((LinearMap.adjoint Jleft).comp (T.comp Jleft)).comp
          V.toLinearEquiv.symm.toLinearMap) := by
      simp only [LinearMap.comp_assoc]
end QEC.Bounds.BPTCommutingProjectorModel

-- Prove2me | solution 1 for QEC.Bounds.complementEmbedding_intertwines_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:09:37.339648+00:00
-- url     : https://prove2.me/submissions/f329e3fc-66ae-4b67-b7c5-c72d06d10eac

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_TensorCoordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_ComplementIntertwiningCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_tensorAssociator_symm_right_intertwines
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
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
open scoped TensorProduct
universe u
set_option maxHeartbeats 180000
set_option synthInstance.maxHeartbeats 60000
namespace QEC.Bounds
theorem _root_.solution
    {W N C D H : Type u}
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (split : Semantics.UnitaryTransport H (Semantics.CompositeSystem C D))
    (eC : Semantics.CompositeSystem W N →ₗ[Complex] C)
    (Z : Semantics.Operator D) :
    let reassociate := BPTCommutingProjectorModel.tensorAssociatorUnitary W N D
    let J := TensorProduct.map eC (1 : Semantics.Operator D)
    let Ecd := J.comp reassociate.symm.toLinearEquiv.toLinearMap
    let P : Semantics.Operator (Semantics.CompositeSystem C D) :=
      TensorProduct.map (1 : Semantics.Operator C) Z
    let Pin : Semantics.Operator (Semantics.CompositeSystem W
        (Semantics.CompositeSystem N D)) :=
      TensorProduct.map (1 : Semantics.Operator W)
        (TensorProduct.map (1 : Semantics.Operator N) Z)
    (split.symm.conjOperator P).comp
        (split.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (split.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Pin := by
  dsimp
  let reassociate := BPTCommutingProjectorModel.tensorAssociatorUnitary W N D
  let J := TensorProduct.map eC (1 : Semantics.Operator D)
  let Ecd := J.comp reassociate.symm.toLinearEquiv.toLinearMap
  let P : Semantics.Operator (Semantics.CompositeSystem C D) :=
    TensorProduct.map (1 : Semantics.Operator C) Z
  let Pmid : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem W N) D) :=
    TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem W N)) Z
  let Pin : Semantics.Operator (Semantics.CompositeSystem W
      (Semantics.CompositeSystem N D)) :=
    TensorProduct.map (1 : Semantics.Operator W)
      (TensorProduct.map (1 : Semantics.Operator N) Z)
  have hOuter : (split.symm.conjOperator P).comp
      split.symm.toLinearEquiv.toLinearMap =
      split.symm.toLinearEquiv.toLinearMap.comp P := by
    unfold Semantics.UnitaryTransport.conjOperator
    simp only [LinearMap.comp_assoc]
    simp
  have hTensor : P.comp J = J.comp Pmid := by
    apply LinearMap.ext
    intro vector
    induction vector using TensorProduct.induction_on with
    | zero => rfl
    | tmul wn d =>
        induction wn using TensorProduct.induction_on with
        | zero => rfl
        | tmul w n => rfl
        | add first second hfirst hsecond =>
            simpa only [TensorProduct.add_tmul, map_add] using
              congrArg₂ (· + ·) hfirst hsecond
    | add first second hfirst hsecond =>
        simpa only [map_add] using congrArg₂ (· + ·) hfirst hsecond
  have hAssociator : Pmid.comp reassociate.symm.toLinearEquiv.toLinearMap =
      reassociate.symm.toLinearEquiv.toLinearMap.comp Pin := by
    simpa [Pmid, Pin, reassociate] using
      (tensorAssociator_symm_right_intertwines
        (H := W) (K := N) Z)
  have hEcd : P.comp Ecd = Ecd.comp Pin := by
    calc
      P.comp Ecd = (P.comp J).comp reassociate.symm.toLinearEquiv.toLinearMap := by
        rfl
      _ = (J.comp Pmid).comp reassociate.symm.toLinearEquiv.toLinearMap := by
        rw [hTensor]
      _ = J.comp (Pmid.comp reassociate.symm.toLinearEquiv.toLinearMap) := by
        rw [← LinearMap.comp_assoc]
      _ = J.comp (reassociate.symm.toLinearEquiv.toLinearMap.comp Pin) := by
        rw [hAssociator]
      _ = Ecd.comp Pin := by
        rfl
  calc
    (split.symm.conjOperator P).comp
        (split.symm.toLinearEquiv.toLinearMap.comp Ecd) =
      (split.symm.toLinearEquiv.toLinearMap.comp P).comp Ecd := by
        rw [← LinearMap.comp_assoc, hOuter]
    _ = split.symm.toLinearEquiv.toLinearMap.comp (P.comp Ecd) := by
      rw [LinearMap.comp_assoc]
    _ = split.symm.toLinearEquiv.toLinearMap.comp (Ecd.comp Pin) := by
      rw [hEcd]
    _ = (split.symm.toLinearEquiv.toLinearMap.comp Ecd).comp Pin := by
      rw [← LinearMap.comp_assoc]
end QEC.Bounds

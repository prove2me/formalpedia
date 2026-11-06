-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.sequential_secondCut_named_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:08:51.162648+00:00
-- url     : https://prove2.me/submissions/52907a81-01d6-40a0-b567-a53dd9a1e64f

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_secondCut_block_of_intertwining
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_comp_tensorMap_right
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
    {A H W N C C' X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2))
    (i : C →ₗ[Complex] C')
    (R : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C' D)))
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D)))
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem N
        (Semantics.CompositeSystem X (Semantics.CompositeSystem N2 D))))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D))
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))))
    (hRsequential :
      let K := TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
        (TensorProduct.map i (1 : Semantics.Operator D))
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hQright :
      let Kright := TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map i (1 : Semantics.Operator D))
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      Qright = (unitaryLTensor N V).conjOperator
        ((LinearMap.adjoint Kright).comp (Q.comp Kright)))
    (hG :
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
        (composeUnitaryTransport
          (unitaryLTensor (Semantics.CompositeSystem A W) (unitaryLTensor N V))
          (unitaryLTensor (Semantics.CompositeSystem A W)
            (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm)))
    (hblock :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm).conjOperator
        (TensorProduct.map P Qright) := by
  dsimp only at hRsequential hQright hG
  subst Rsequential
  subst Qright
  subst G
  have hintertwines := isotypicSectorBlockTransportLeft_comp_tensorMap_right
    (A := A) (H := H) (W := W) (N := N)
    (C := Semantics.CompositeSystem C D)
    (C' := Semantics.CompositeSystem C' D) UB
    (TensorProduct.map i (1 : Semantics.Operator D))
  exact sequential_secondCut_block_of_intertwining UB UC i R P Q hblock hintertwines
end QEC.Bounds.BPTCommutingProjectorModel

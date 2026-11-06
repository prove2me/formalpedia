-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.sequential_firstCut_named_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:26:29.218078+00:00
-- url     : https://prove2.me/submissions/5c64b2d8-a426-4652-bcd1-11bc056d5d35

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_firstCut_block_of_left_intertwining
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
    {A B B' H W N D WB NB : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup B'] [InnerProductSpace Complex B'] [Semantics.FiniteQuantumSystem B']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    (UC : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UB : Semantics.UnitaryTransport B (Semantics.CompositeSystem WB NB))
    (i : B →ₗ[Complex] B')
    (R : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B') H) D))
    (P : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B') W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N D))
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W)))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D)
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem (Semantics.CompositeSystem NB W)
          (Semantics.CompositeSystem N D))))
    (hRsequential :
      let K := TensorProduct.map
        (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
          (1 : Semantics.Operator H))
        (1 : Semantics.Operator D)
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hPleft :
      let Kleft := TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator W)
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      Pleft = TB.conjOperator ((LinearMap.adjoint Kleft).comp (P.comp Kleft)))
    (hG :
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
        (composeUnitaryTransport
          (unitaryRTensor TB (Semantics.CompositeSystem N D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
            (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D))))
    (hblock :
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)).conjOperator
        (TensorProduct.map Pleft Q) := by
  dsimp only at hRsequential hPleft hG
  subst Rsequential
  subst Pleft
  subst G
  exact sequential_firstCut_block_of_left_intertwining UC UB i R P Q hblock
end QEC.Bounds.BPTCommutingProjectorModel

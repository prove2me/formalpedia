-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.sequential_isotypicSectorBlockTransportLeft_coherence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:45:53.388893+00:00
-- url     : https://prove2.me/submissions/3c4f5912-e841-4603-8fb2-a8a1e0a26cc7

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_ext
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


attribute [local simp] QEC.Bounds.BPTCommutingProjectorModel.isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    {A H W N C X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2)) :
    composeUnitaryTransport
        (tensorAssociatorUnitary (Semantics.CompositeSystem A H) C D)
        (composeUnitaryTransport
          (isotypicSectorBlockTransportLeft A H W N
            (Semantics.CompositeSystem C D) UB)
          (composeUnitaryTransport
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (unitaryLTensor N
                (composeUnitaryTransport (unitaryRTensor UC D)
                  (tensorAssociatorUnitary X N2 D))))
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))) =
      composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A H) C X N2 D UC)
        (composeUnitaryTransport
          (unitaryRTensor (isotypicSectorBlockTransportLeft A H W N X UB)
            (Semantics.CompositeSystem N2 D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A W)
            (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))) := by
  apply unitaryTransport_ext
  apply LinearEquiv.ext
  intro vector
  induction vector using TensorProduct.induction_on with
  | zero => simpa only [map_zero]
  | tmul abc d =>
      induction abc using TensorProduct.induction_on with
      | zero => simpa only [TensorProduct.zero_tmul, map_zero]
      | tmul ab c =>
          induction ab using TensorProduct.induction_on with
          | zero => simpa only [TensorProduct.zero_tmul, map_zero]
          | tmul a h =>
              rcases UB.symm.toLinearEquiv.surjective h with ⟨wn, hwn⟩
              subst h
              induction wn using TensorProduct.induction_on with
              | zero =>
                  simpa only [map_zero, TensorProduct.tmul_zero,
                    TensorProduct.zero_tmul]
              | tmul w n =>
                  rcases UC.symm.toLinearEquiv.surjective c with ⟨xn, hxn⟩
                  subst c
                  induction xn using TensorProduct.induction_on with
                  | zero =>
                      simpa only [map_zero, TensorProduct.tmul_zero,
                        TensorProduct.zero_tmul]
                  | tmul x n2 =>
                      have hUB : UB (UB.symm (w ⊗ₜ[Complex] n)) =
                          w ⊗ₜ[Complex] n := by simp
                      have hUC : UC (UC.symm (x ⊗ₜ[Complex] n2)) =
                          x ⊗ₜ[Complex] n2 := by simp
                      simp only [composeUnitaryTransport_toLinearEquiv_apply]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A H) C D
                        (a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2)) d]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UB a
                        (UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d) w n hUB]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (unitaryLTensor N
                          (composeUnitaryTransport (unitaryRTensor UC D)
                            (tensorAssociatorUnitary X N2 D)))
                        (a ⊗ₜ[Complex] w)
                        (n ⊗ₜ[Complex] (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d))]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul N
                        (composeUnitaryTransport (unitaryRTensor UC D)
                          (tensorAssociatorUnitary X N2 D)) n
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d)]
                      rw [composeUnitaryTransport_toLinearEquiv_apply
                        (unitaryRTensor UC D) (tensorAssociatorUnitary X N2 D)
                        (UC.symm (x ⊗ₜ[Complex] n2) ⊗ₜ[Complex] d)]
                      rw [unitaryRTensor_toLinearEquiv_apply_tmul UC D
                        (UC.symm (x ⊗ₜ[Complex] n2)) d, hUC]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul X N2 D x n2 d]
                      rw [unitaryLTensor_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm
                        (a ⊗ₜ[Complex] w)
                        (n ⊗ₜ[Complex] (x ⊗ₜ[Complex] (n2 ⊗ₜ[Complex] d)))]
                      rw [tensorAssociatorUnitary_symm_toLinearEquiv_apply_tmul N X
                        (Semantics.CompositeSystem N2 D) n x (n2 ⊗ₜ[Complex] d)]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UC
                        (a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n))
                        (UC.symm (x ⊗ₜ[Complex] n2)) d x n2 hUC]
                      rw [unitaryRTensor_toLinearEquiv_apply_tmul
                        (isotypicSectorBlockTransportLeft A H W N X UB)
                        (Semantics.CompositeSystem N2 D)
                        ((a ⊗ₜ[Complex] UB.symm (w ⊗ₜ[Complex] n)) ⊗ₜ[Complex] x)
                        (n2 ⊗ₜ[Complex] d)]
                      rw [isotypicSectorBlockTransportLeft_toLinearEquiv_apply_tmul_of_apply_eq UB a
                        (UB.symm (w ⊗ₜ[Complex] n)) x w n hUB]
                      rw [tensorAssociatorUnitary_toLinearEquiv_apply_tmul
                        (Semantics.CompositeSystem A W)
                        (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D)
                        (a ⊗ₜ[Complex] w) (n ⊗ₜ[Complex] x)
                        (n2 ⊗ₜ[Complex] d)]
                  | add first second hfirst hsecond =>
                      rw [map_add]
                      rw [TensorProduct.tmul_add, TensorProduct.add_tmul]
                      rw [map_add, map_add]
                      exact congrArg₂ (· + ·) hfirst hsecond
              | add first second hfirst hsecond =>
                  rw [map_add]
                  rw [TensorProduct.tmul_add, TensorProduct.add_tmul,
                    TensorProduct.add_tmul]
                  rw [map_add, map_add]
                  exact congrArg₂ (· + ·) hfirst hsecond
          | add first second hfirst hsecond =>
              rw [TensorProduct.add_tmul, TensorProduct.add_tmul]
              rw [map_add, map_add]
              exact congrArg₂ (· + ·) hfirst hsecond
      | add first second hfirst hsecond =>
          rw [TensorProduct.add_tmul]
          rw [map_add, map_add]
          exact congrArg₂ (· + ·) hfirst hsecond
  | add first second hfirst hsecond =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hfirst hsecond
end QEC.Bounds.BPTCommutingProjectorModel

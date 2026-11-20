-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.disentangled_prepareSelected_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:29:53.289738+00:00
-- url     : https://prove2.me/submissions/8707c2b9-c2ce-4401-bc09-9ad7509f6056

import Definitions.Def_QEC_Bounds_BPTDisentangling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
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
import Theorems.Thm_QEC_Semantics_DensityOperator_supportedOn_projector_comp_eq_self
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareFactorized_erasure_fixed_of_supportedOn_branch
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_replacementFactorizedKraus_operator
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceReordering_apply_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceTransport_apply_tmul
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjOperator_comp
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


section
noncomputable section
namespace QEC
namespace Bounds
namespace BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
private theorem tensorMap_rankOne_left_range
    (H K : Type u) [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (phi : H) (P : Operator K)
    (z : CompositeSystem H K) :
    TensorProduct.map (InnerProductSpace.rankOne Complex phi phi).toLinearMap P z ∈
      LinearMap.range (prepareLeftBranch H K phi) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      simp [prepareLeftBranch]
  | tmul h k =>
      refine ⟨(inner Complex phi h) • P k, ?_⟩
      simp [prepareLeftBranch, InnerProductSpace.rankOne_apply,
        TensorProduct.smul_tmul]
  | add x y hx hy =>
      rcases hx with ⟨x, hx⟩
      rcases hy with ⟨y, hy⟩
      refine ⟨x + y, ?_⟩
      simpa [map_add, hx, hy] using congrArg₂ (· + ·) hx hy
end BPTCommutingProjectorModel
end Bounds
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open Semantics
open Semantics.DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (unitary : UnitaryTransport L.Register L.Register)
    (regionalState : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Operator (M.regionSubsystem region).complementSystem)
    (unitary_supported : M.UnitarySupportedOn (M.boundary region) unitary)
    (regionalState_normalized : ‖regionalState‖ = 1)
    (projector_factorization :
      unitary.conjOperator M.fullCodeProjector =
        M.pureFactorTensorComplementProjector region regionalState complementProjector)
    (rho : DensityOperator L.Register)
    (hsupported : DensityOperator.SupportedOn M.codeSpace rho) :
    (M.regionSubsystem region).prepareSelected
      (pureDensity regionalState (by rw [regionalState_normalized]; norm_num))
      ((M.regionSubsystem region).erasureChannelFromRegister
        (unitary.conjOperator rho.toOperator)) =
      unitary.conjOperator rho.toOperator := by
  let S := M.regionSubsystem region
  let rhoU := unitary.conjDensity rho
  have hcode : M.fullCodeProjector.comp rho.toOperator = rho.toOperator :=
    DensityOperator.supportedOn_projector_comp_eq_self M.codeSpace rho hsupported
  have hunitaryCode : (unitary.conjOperator M.fullCodeProjector).comp rhoU.toOperator =
      rhoU.toOperator := by
    change (unitary.conjOperator M.fullCodeProjector).comp
        (unitary.conjOperator rho.toOperator) = unitary.conjOperator rho.toOperator
    rw [← unitary.conjOperator_comp, hcode]
  have hcoordinateCode :
      (TensorProduct.map (InnerProductSpace.rankOne Complex regionalState regionalState).toLinearMap
        complementProjector).comp (S.registerFactorization.conjOperator rhoU.toOperator) =
        S.registerFactorization.conjOperator rhoU.toOperator := by
    calc
      (TensorProduct.map
          (InnerProductSpace.rankOne Complex regionalState regionalState).toLinearMap
          complementProjector).comp (S.registerFactorization.conjOperator rhoU.toOperator) =
          S.registerFactorization.conjOperator
            ((M.pureFactorTensorComplementProjector region regionalState complementProjector).comp
              rhoU.toOperator) := by
            symm
            unfold BPTCommutingProjectorModel.pureFactorTensorComplementProjector
            rw [S.registerFactorization.conjOperator_comp]
            rw [S.registerFactorization.conjOperator_symm_conjOperator]
      _ = S.registerFactorization.conjOperator
            ((unitary.conjOperator M.fullCodeProjector).comp rhoU.toOperator) := by
            rw [projector_factorization]
      _ = S.registerFactorization.conjOperator rhoU.toOperator := by rw [hunitaryCode]
  have hbranch : ∀ z : S.factorizedSystem,
      (S.registerFactorization.conjOperator rhoU.toOperator) z ∈
        LinearMap.range (S.prepareFactorizedBranch regionalState) := by
    intro z
    rw [← hcoordinateCode]
    simp only [LinearMap.comp_apply]
    exact tensorMap_rankOne_left_range S.selectedSystem S.complementSystem
      regionalState complementProjector (S.registerFactorization.conjOperator rhoU.toOperator z)
  have hprepared := S.prepareFactorized_erasure_fixed_of_supportedOn_branch
    regionalState (by rw [regionalState_normalized]; norm_num)
    (S.registerFactorization.conjDensity rhoU) hbranch
  change S.registerFactorization.symm.conjOperator
      (S.prepareFactorized (pureDensity regionalState (by rw [regionalState_normalized]; norm_num))
        (S.erasureChannel (S.registerFactorization.conjOperator rhoU.toOperator))) =
      rhoU.toOperator
  rw [← S.registerFactorization.conjDensity_toOperator]
  rw [hprepared]
  exact S.registerFactorization.symm_conjOperator_conjOperator rhoU.toOperator
end QEC.Bounds.BPTCommutingProjectorModel

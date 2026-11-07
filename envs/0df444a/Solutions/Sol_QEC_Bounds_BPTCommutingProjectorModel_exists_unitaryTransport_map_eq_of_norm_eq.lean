-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.exists_unitaryTransport_map_eq_of_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:31:20.092708+00:00
-- url     : https://prove2.me/submissions/b9dbeced-5ab9-4d53-a7fd-f364031e689d

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductUnitary
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
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (x y : H) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ U : Semantics.UnitaryTransport H H, U x = y := by
  classical
  have hx0 : x ≠ 0 := by
    intro hzero
    have hzero_one : (0 : ℝ) = 1 := by simpa [hzero] using hx
    norm_num at hzero_one
  letI : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
  have hdimpos : 0 < Module.finrank Complex H := Module.finrank_pos_iff.mpr inferInstance
  let i0 : Fin (Module.finrank Complex H) := ⟨0, hdimpos⟩
  let s : Set (Fin (Module.finrank Complex H)) := {i0}
  let vx : Fin (Module.finrank Complex H) → H := fun _ => x
  let vy : Fin (Module.finrank Complex H) → H := fun _ => y
  letI : Subsingleton s := ⟨fun a b => by
    apply Subtype.ext
    have ha_mem : (a : Fin (Module.finrank Complex H)) ∈ ({i0} : Set _) := by
      change (a : Fin (Module.finrank Complex H)) ∈ s
      exact a.property
    have hb_mem : (b : Fin (Module.finrank Complex H)) ∈ ({i0} : Set _) := by
      change (b : Fin (Module.finrank Complex H)) ∈ s
      exact b.property
    have ha : (a : Fin (Module.finrank Complex H)) = i0 := Set.mem_singleton_iff.mp ha_mem
    have hb : (b : Fin (Module.finrank Complex H)) = i0 := Set.mem_singleton_iff.mp hb_mem
    exact ha.trans hb.symm⟩
  have hvx : Orthonormal Complex (s.restrict vx) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hx
  have hvy : Orthonormal Complex (s.restrict vy) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    exact hy
  obtain ⟨bx, hbx⟩ := hvx.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (Module.finrank Complex H)) (by simp)
  obtain ⟨bY, hbY⟩ := hvy.exists_orthonormalBasis_extension_of_card_eq
    (ι := Fin (Module.finrank Complex H)) (by simp)
  have hbx0 : bx i0 = x := by
    simpa [vx] using hbx i0 (by simp [s])
  have hbY0 : bY i0 = y := by
    simpa [vy] using hbY i0 (by simp [s])
  let E : H ≃ₗᵢ[Complex] H := bx.equiv bY (Equiv.refl _)
  let U : Semantics.UnitaryTransport H H :=
    { toLinearEquiv := E.toLinearEquiv
      map_inner := fun a b => E.inner_map_map a b }
  have hU : U x = y := by
    change E x = y
    calc
      E x = E (bx i0) := by rw [hbx0]
      _ = bY i0 := by
        simpa [E] using bx.equiv_apply_basis bY (Equiv.refl _) i0
      _ = y := hbY0
  exact ⟨U, hU⟩
end QEC.Bounds.BPTCommutingProjectorModel

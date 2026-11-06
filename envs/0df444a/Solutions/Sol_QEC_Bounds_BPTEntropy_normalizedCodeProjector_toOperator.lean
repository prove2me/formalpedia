-- Prove2me | solution 1 for QEC.Bounds.BPTEntropy.normalizedCodeProjector_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:29:11.528491+00:00
-- url     : https://prove2.me/submissions/c2cd4a0d-bb4d-4f05-8983-5bce2d40cccc

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_Entropy_Subadditivity
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Theorems.Thm_QEC_Bounds_BPTEntropy_sum_code_basis_eq_projector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_mem_regionSubsystem_selected_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionSubsystem_selected
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_DensityOperator_rankOne_sum_sum
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
import Theorems.Thm_QEC_Semantics_QuditSubsystem_partialTraceRightRaw_rankOne_tmul
import Theorems.Thm_QEC_Semantics_QuditSubsystem_registerFactorizationWithReference_apply_tmul
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
open QEC.Bounds.BPTEntropy
open Semantics
open Semantics.DensityOperator
universe u
namespace QEC.Bounds.BPTEntropy
theorem _root_.solution {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (C : QuantumCode H) (hdim : 0 < C.dimension) :
    (normalizedCodeProjector C hdim).toOperator =
      ((C.dimension : Real)⁻¹ : Complex) • C.projector := by
  classical
  unfold normalizedCodeProjector
  let e : Fin C.dimension → H := fun i =>
    ((stdOrthonormalBasis Complex C.carrier i : C.carrier) : H)
  have he_inner (i j : Fin C.dimension) :
      inner Complex (e i) (e j) = if i = j then 1 else 0 :=
    (stdOrthonormalBasis Complex C.carrier).inner_eq_ite i j
  let a : Complex := Real.sqrt ((C.dimension : Real)⁻¹)
  change partialTraceRightRaw H H
    ((InnerProductSpace.rankOne Complex
      (∑ i, (a • e i) ⊗ₜ[Complex] e i)
      (∑ j, (a • e j) ⊗ₜ[Complex] e j)).toLinearMap) = _
  rw [rankOne_sum_sum]
  simp only [map_sum]
  simp_rw [QuditSubsystem.partialTraceRightRaw_rankOne_tmul]
  simp only [he_inner, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp
  simp_rw [smul_comm a ((starRingEnd Complex) a)]
  change ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
      (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap = _
  have hscalar : (starRingEnd Complex) a * a = ((C.dimension : Real)⁻¹ : Complex) := by
    change star (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) *
      (Real.sqrt ((C.dimension : Real)⁻¹) : Complex) = _
    rw [Complex.star_def, Complex.conj_ofReal]
    exact_mod_cast (show Real.sqrt ((C.dimension : Real)⁻¹) *
        Real.sqrt ((C.dimension : Real)⁻¹) = (C.dimension : Real)⁻¹ by
      simpa [pow_two] using Real.sq_sqrt (inv_nonneg.mpr (by positivity)))
  calc
    ∑ x : Fin C.dimension, (starRingEnd Complex) a • a •
        (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap =
        ∑ x, ((C.dimension : Real)⁻¹ : Complex) •
          (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_smul, hscalar]
    _ = ((C.dimension : Real)⁻¹ : Complex) •
        ∑ x, (InnerProductSpace.rankOne Complex (e x) (e x)).toLinearMap :=
      (Finset.smul_sum).symm
    _ = ((C.dimension : Real)⁻¹ : Complex) • C.projector := by
      simp only [e]
      rw [sum_code_basis_eq_projector]
end QEC.Bounds.BPTEntropy

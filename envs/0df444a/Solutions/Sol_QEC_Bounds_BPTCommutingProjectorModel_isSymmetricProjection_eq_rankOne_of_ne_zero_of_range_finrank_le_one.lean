-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.isSymmetricProjection_eq_rankOne_of_ne_zero_of_range_finrank_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:04:07.263195+00:00
-- url     : https://prove2.me/submissions/8272856c-86ad-41fa-9d1f-09d982287635

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Compression
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_RankOne
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
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection) (hP0 : P ≠ 0)
    (hdim : Module.finrank Complex (LinearMap.range P) ≤ 1) :
    ∃ phi : H, ‖phi‖ = 1 ∧
      P = (InnerProductSpace.rankOne Complex phi phi).toLinearMap := by
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hP0
  let v : H := P x
  have hv : v ≠ 0 := by
    simpa [v] using hx
  let vRange : LinearMap.range P := ⟨v, x, rfl⟩
  have hvRange : vRange ≠ 0 := by
    intro hzero
    apply hv
    have hcoerce := congrArg (fun z : LinearMap.range P => (z : H)) hzero
    simpa [vRange] using hcoerce
  have hpositive : 0 < Module.finrank Complex (LinearMap.range P) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨vRange, hvRange⟩
  have hdimEq : Module.finrank Complex (LinearMap.range P) = 1 := by
    apply Nat.le_antisymm hdim
    exact Nat.succ_le_iff.mpr hpositive
  let phi : H := (‖v‖ : Complex)⁻¹ • v
  have hnormv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hphi : ‖phi‖ = 1 := by
    dsimp [phi]
    rw [norm_smul, norm_inv]
    simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)] using
      inv_mul_cancel₀ hnormv
  have hscale : (‖v‖ : Complex) • phi = v := by
    calc
      (‖v‖ : Complex) • phi =
          (‖v‖ : Complex) • ((‖v‖ : Complex)⁻¹ • v) := by rfl
      _ = ((‖v‖ : Complex) * (‖v‖ : Complex)⁻¹) • v :=
        (mul_smul (‖v‖ : Complex) (‖v‖ : Complex)⁻¹ v).symm
      _ = v := by
        rw [mul_inv_cancel₀]
        · exact one_smul Complex v
        · exact_mod_cast hnormv
  have hrange : LinearMap.range P = Submodule.span Complex {phi} := by
    apply le_antisymm
    · intro y hy
      let yRange : LinearMap.range P := ⟨y, hy⟩
      rcases exists_smul_eq_of_finrank_eq_one hdimEq hvRange yRange with
        ⟨scalar, hscalar⟩
      rw [Submodule.mem_span_singleton]
      refine ⟨scalar * (‖v‖ : Complex), ?_⟩
      change (scalar * (‖v‖ : Complex)) • phi = y
      calc
        (scalar * (‖v‖ : Complex)) • phi = scalar • ((‖v‖ : Complex) • phi) := by
          exact mul_smul scalar (‖v‖ : Complex) phi
        _ = scalar • v := by rw [hscale]
        _ = y := congrArg Subtype.val hscalar
    · refine Submodule.span_le.2 ?_
      intro z hz
      have hzphi : z = phi := by simpa using hz
      subst z
      dsimp [phi]
      exact (LinearMap.range P).smul_mem _ ⟨x, rfl⟩
  let R : Semantics.Operator H := (InnerProductSpace.rankOne Complex phi phi).toLinearMap
  have hR : R.IsSymmetricProjection := by
    simpa [R] using
      (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hphi)
  have hrangeR : LinearMap.range R = Submodule.span Complex {phi} := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      change (inner Complex phi z) • phi ∈ Submodule.span Complex {phi}
      exact (Submodule.span Complex {phi}).smul_mem _
        (Submodule.mem_span_singleton_self phi)
    · refine Submodule.span_le.2 ?_
      intro z hz
      have hzphi : z = phi := by simpa using hz
      subst z
      refine ⟨phi, ?_⟩
      change (inner Complex phi phi) • phi = phi
      rw [inner_self_eq_norm_sq_to_K]
      simpa [hphi]
  have hrangePR : LinearMap.range P = LinearMap.range R :=
    hrange.trans hrangeR.symm
  letI : (LinearMap.range P).HasOrthogonalProjection :=
    hP.hasOrthogonalProjection_range
  have projection_residual_orthogonal
      (T : Semantics.Operator H) (hT : T.IsSymmetricProjection)
      {z : H} : z - T z ∈ (LinearMap.range T)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    rcases hy with ⟨w, rfl⟩
    have hidem : T (T w) = T w := by
      change (T * T) w = T w
      rw [hT.isIdempotentElem]
    rw [inner_sub_left]
    calc
      inner Complex z (T w) - inner Complex (T z) (T w) =
          inner Complex z (T w) - inner Complex z (LinearMap.adjoint T (T w)) := by
            rw [LinearMap.adjoint_inner_right]
      _ = inner Complex z (T w) - inner Complex z (T w) := by
            rw [hT.isSymmetric.adjoint_eq, hidem]
      _ = 0 := sub_self _
  refine ⟨phi, hphi, ?_⟩
  apply LinearMap.ext
  intro z
  have hPmem : P z ∈ LinearMap.range P := ⟨z, rfl⟩
  have hPperp : z - P z ∈ (LinearMap.range P)ᗮ :=
    projection_residual_orthogonal P hP
  have hPstar : P z = (LinearMap.range P).starProjection z :=
    (Submodule.eq_starProjection_of_mem_orthogonal hPmem hPperp).symm
  have hRmem : R z ∈ LinearMap.range P := by
    rw [hrangePR]
    exact ⟨z, rfl⟩
  have hRperp : z - R z ∈ (LinearMap.range P)ᗮ := by
    rw [hrangePR]
    exact projection_residual_orthogonal R hR
  have hRstar : R z = (LinearMap.range P).starProjection z :=
    (Submodule.eq_starProjection_of_mem_orthogonal hRmem hRperp).symm
  rw [hPstar, hRstar]
end QEC.Bounds.BPTCommutingProjectorModel

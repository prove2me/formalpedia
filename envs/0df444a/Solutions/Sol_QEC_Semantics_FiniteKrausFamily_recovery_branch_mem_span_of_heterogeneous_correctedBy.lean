-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_heterogeneous_correctedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:53:41.38121+00:00
-- url     : https://prove2.me/submissions/9f198ca0-5ac1-4ec1-87ae-e93fed730f47

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_DensityOperator_comp_pureOfNonzero_adjoint
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_supportedOn
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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
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
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.FiniteKrausFamily
variable {H : Type u} {K : Type u} {ι : Type v} {κ : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [Fintype ι] [Fintype κ]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H K) (C : QuantumCode H)
    (R : κ → K →ₗ[Complex] H)
    (hcorrect : ∀ rho : DensityOperator H,
      DensityOperator.SupportedOn C rho →
        (∑ r : κ, (R r).comp
          ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r)))) =
          rho.toOperator)
    (r : κ) (i : ι) {x : H} (hxC : x ∈ C.carrier) :
    R r (E.operator i x) ∈ Complex ∙ x := by
  classical
  by_cases hx0 : x = 0
  · subst x
    simp
  let rho : DensityOperator H := DensityOperator.pureOfNonzero x hx0
  let term : κ → ι → Operator H := fun r i =>
    ((R r).comp (E.operator i)).comp
      (rho.toOperator.comp (LinearMap.adjoint ((R r).comp (E.operator i))))
  have hsum : (∑ r : κ, ∑ i : ι, term r i) = rho.toOperator := by
    calc
      (∑ r : κ, ∑ i : ι, term r i)
          = ∑ r : κ, (R r).comp
              ((E.inducedMap rho.toOperator).comp (LinearMap.adjoint (R r))) := by
            ext y
            simp [term, FiniteKrausFamily.inducedMap_apply,
              LinearMap.adjoint_comp, Finset.sum_apply]
      _ = rho.toOperator := hcorrect rho
        (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
  have hmem_double : R r (E.operator i x) ∈ (Complex ∙ x)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hxy : inner Complex x y = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy
    have hRhoY : rho.toOperator y = 0 := by
      simp [rho, hxy]
    have hquad : (∑ r : κ, ∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hyop := congrArg (fun A : Operator H => inner Complex (A y) y) hsum
      simpa [term, Finset.sum_apply, hRhoY] using hyop
    have hterm_pos : ∀ r i, LinearMap.IsPositive (term r i) := by
      intro r i
      change LinearMap.IsPositive
        (((R r).comp (E.operator i)).comp
          ((DensityOperator.pureOfNonzero x hx0).toOperator.comp
            (LinearMap.adjoint ((R r).comp (E.operator i)))))
      rw [DensityOperator.comp_pureOfNonzero_adjoint]
      have hpos : LinearMap.IsPositive
          (((InnerProductSpace.rankOne Complex (((R r).comp (E.operator i)) x)
            (((R r).comp (E.operator i)) x) : H →L[Complex] H) :
              H →ₗ[Complex] H)) := by
        exact (InnerProductSpace.isPositive_rankOne_self (𝕜 := Complex)
          (((R r).comp (E.operator i)) x)).toLinearMap
      have hinner_nonneg : 0 ≤ inner Complex x x := by
        rw [inner_self_eq_norm_sq_to_K]
        positivity
      exact hpos.smul_of_nonneg ((inv_nonneg).2 hinner_nonneg)
    have houter_zero : (∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hfun : (fun r : κ => ∑ i : ι, inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro r
          exact Finset.sum_nonneg (by
            intro i _hi
            exact (hterm_pos r i).inner_nonneg_left y))).mp hquad
      exact congrFun hfun r
    have hinner_zero : inner Complex ((term r i) y) y = 0 := by
      have hfun : (fun i : ι => inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro i
          exact (hterm_pos r i).inner_nonneg_left y)).mp houter_zero
      exact congrFun hfun i
    let A : Operator H := (R r).comp (E.operator i)
    have hinner_rank :
        inner Complex
          (((((inner Complex x x)⁻¹ •
            (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
              H →ₗ[Complex] H))) : H →ₗ[Complex] H) y)) y = 0 := by
      have hterm_eq := DensityOperator.comp_pureOfNonzero_adjoint A x hx0
      rw [← hterm_eq]
      simpa [A, term, rho] using hinner_zero
    have hc_ne : (inner Complex x x)⁻¹ ≠ 0 := inv_ne_zero (inner_self_ne_zero.mpr hx0)
    have h' :
        (inner Complex x x)⁻¹ * (inner Complex (A x) y * inner Complex y (A x)) = 0 := by
      simpa [inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using hinner_rank
    have hprod : inner Complex (A x) y * inner Complex y (A x) = 0 := by
      exact (mul_eq_zero.mp h').resolve_left hc_ne
    have hAxy : inner Complex (A x) y = 0 := by
      rcases mul_eq_zero.mp hprod with hz | hy'
      · exact hz
      · exact inner_eq_zero_symm.mp hy'
    simpa [A, LinearMap.comp_apply] using hAxy
  rw [Submodule.orthogonal_orthogonal] at hmem_double
  exact hmem_double
end QEC.Semantics.FiniteKrausFamily

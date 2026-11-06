-- Prove2me | solution 1 for QEC.Semantics.FiniteKrausFamily.recovery_branch_mem_span_of_finiteKraus_correctedBy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:34:29.671714+00:00
-- url     : https://prove2.me/submissions/21b3df0d-99f9-4f14-b17a-7f0107a010ec

import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Theorems.Thm_QEC_Semantics_DensityOperator_comp_pureOfNonzero_adjoint
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_apply
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_supportedOn
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
import Theorems.Thm_QEC_Semantics_OperatorMatrix_matrixUnit_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_apply
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.OperatorMatrix.matrixUnit_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator



set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {κ : Type w} [Fintype κ]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
namespace QEC.Semantics.FiniteKrausFamily
theorem _root_.solution
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H)
    (R : κ → KrausOperator H H)
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
      _ = rho.toOperator := hcorrect rho (DensityOperator.pureOfNonzero_supportedOn hx0 hxC)
  have hmem_double : R r (E.operator i x) ∈ (Complex ∙ x)ᗮᗮ := by
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hxy : inner Complex x y = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).1 hy
    have hρy : rho.toOperator y = 0 := by
      simp [rho, hxy]
    have hquad : (∑ r : κ, ∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hyop := congrArg (fun A : Operator H => inner Complex (A y) y) hsum
      simpa [term, Finset.sum_apply, hρy] using hyop
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
    have h_outer_zero : (∑ i : ι, inner Complex ((term r i) y) y) = 0 := by
      have hfun : (fun r : κ => ∑ i : ι, inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro r
          exact Finset.sum_nonneg (by
            intro i _hi
            exact (hterm_pos r i).inner_nonneg_left y))).mp hquad
      exact congrFun hfun r
    have h_inner_zero : inner Complex ((term r i) y) y = 0 := by
      have hfun : (fun i : ι => inner Complex ((term r i) y) y) = 0 :=
        (Fintype.sum_eq_zero_iff_of_nonneg (by
          intro i
          exact (hterm_pos r i).inner_nonneg_left y)).mp h_outer_zero
      exact congrFun hfun i
    let A : Operator H := (R r).comp (E.operator i)
    have h_inner_rank :
        inner Complex
          (((((inner Complex x x)⁻¹ •
            (((InnerProductSpace.rankOne Complex (A x) (A x) : H →L[Complex] H) :
              H →ₗ[Complex] H))) : H →ₗ[Complex] H) y)) y = 0 := by
      have hterm_eq := DensityOperator.comp_pureOfNonzero_adjoint A x hx0
      rw [← hterm_eq]
      simpa [A, term, rho] using h_inner_zero
    have hc_ne : (inner Complex x x)⁻¹ ≠ 0 := inv_ne_zero (inner_self_ne_zero.mpr hx0)
    have h' :
        (inner Complex x x)⁻¹ * (inner Complex (A x) y * inner Complex y (A x)) = 0 := by
      simpa [inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using h_inner_rank
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

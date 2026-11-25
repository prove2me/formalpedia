-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartKernel_chartEv_chartSubst_0bbd94b367c7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:59.608403+00:00
-- url     : https://prove2.me/submissions/eae6f64d-c21f-455b-8e18-8aaf82bbfa75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartKernel
variable {F : Type} [Field F] {n : ℕ}
variable (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
namespace GroundTheory.Heights₂.Heights.ChartKernel
theorem _root_.solution (p : MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :
    chartEv I t e (chartSubst I t e p) = Ideal.Quotient.mk (chartIncIdeal I t e) p := by
  have hXl : ∀ m, chartX I t e (X m) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl m)) := fun m =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_X Sum.inl m)
  have hU : ∀ ij, chartIncHom I t e (X ij) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr ij)) := fun ij =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_X Sum.inr ij)
  have hCr : ∀ r, chartX I t e (C r) = Ideal.Quotient.mk (chartIncIdeal I t e) (C r) := fun r =>
    congrArg (Ideal.Quotient.mk (chartIncIdeal I t e)) (rename_C Sum.inl r)
  have h0 : ∀ i : Fin e, ∑ l, chartIncHom I t e (X (i, l)) * chartX I t e (X l) = 0 := by
    intro i
    have : ∑ l, chartIncHom I t e (X (i, l)) * chartX I t e (X l) =
        Ideal.Quotient.mk (chartIncIdeal I t e) (∑ m, X (Sum.inr (i, m)) * X (Sum.inl m)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hU, hXl]
      exact (map_mul _ _ _).symm
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have h : (chartEv I t e).comp (chartSubst I t e) = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_C, RingHom.id_apply]
      exact hCr r
    · rintro (m | ij)
      · simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply,
          Sum.elim_inl]
        exact hXl m
      · simp only [RingHom.comp_apply, chartEv, chartSubst, coe_eval₂Hom, eval₂_X, Sum.elim_inr, genSubst,
          eval₂_sub, eval₂_mul, eval₂_sum, eval₂_C, RingHom.id_apply, h0, zero_mul, sub_zero]
        exact hU ij
  exact RingHom.congr_fun h p
end GroundTheory.Heights₂.Heights.ChartKernel

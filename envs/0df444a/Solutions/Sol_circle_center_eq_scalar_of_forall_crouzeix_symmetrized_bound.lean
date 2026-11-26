-- Prove2me | solution 1 for circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:47.341621+00:00
-- url     : https://prove2.me/submissions/4b00af79-5b25-4d32-ba1f-c974a2dc7272

import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_ProductSymmetrizedAlignment
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange


section
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
omit [CompleteSpace E] in
private theorem numericalRange_smul_one_productAlignment (a : ℂ) :
    numericalRange (a • (1 : E →L[ℂ] E)) = {a} := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ :=
      (mem_numericalRange (a • (1 : E →L[ℂ] E)) _).mp hz
    rw [smul_apply, one_apply_eq_self, inner_smul_right,
      Set.mem_singleton_iff, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    apply (mem_numericalRange (a • (1 : E →L[ℂ] E)) a).mpr
    refine ⟨x, hxnorm, ?_⟩
    rw [smul_apply, one_apply_eq_self, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
end

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
theorem _root_.solution
    (a c : ℂ) {R : ℝ}
    (hA : ‖a • (1 : E →L[ℂ] E) - c • 1‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) q +
          star (crouzeixPolynomialAuxiliaryOperator
            (a • (1 : E →L[ℂ] E))
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange (a • (1 : E →L[ℂ] E))))) :
    c = a := by
  let q : Polynomial ℂ := Polynomial.X - Polynomial.C a
  have hsup : polynomialSupNorm q
      (closure (numericalRange (a • (1 : E →L[ℂ] E)))) = 0 := by
    rw [numericalRange_smul_one_productAlignment a, closure_singleton]
    apply le_antisymm
    · unfold polynomialSupNorm
      refine Real.iSup_le (fun z => ?_) le_rfl
      refine Real.iSup_le (fun hz => ?_) le_rfl
      rw [Set.mem_singleton_iff] at hz
      subst z
      simp only [q, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, sub_self, norm_zero]
      exact le_rfl
    · exact polynomialSupNorm_nonneg q {a}
  have hae : Polynomial.aeval (a • (1 : E →L[ℂ] E)) q = 0 := by
    dsimp only [q]
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, sub_self]
  have hG : crouzeixPolynomialAuxiliaryOperator
      (a • (1 : E →L[ℂ] E))
      (SmoothJordanDomain.ball c R
        ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) q =
      star (Polynomial.eval c q) • (1 : E →L[ℂ] E) :=
    crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      (a • (1 : E →L[ℂ] E)) c hA q
  have h := hsymm q
  rw [hae, hG, hsup] at h
  simp only [zero_add, star_smul, star_one, star_star,
    q, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    mul_zero] at h
  rw [norm_smul, norm_one] at h
  have hle : ‖c - a‖ ≤ 0 := by
    simpa only [mul_one, mul_zero] using h
  have hzero : c - a = 0 := norm_eq_zero.mp
    (le_antisymm hle (norm_nonneg _))
  exact sub_eq_zero.mp hzero

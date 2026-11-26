-- Prove2me | solution 1 for circle_center_mem_of_isCompact_nonempty_convex_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:34.744326+00:00
-- url     : https://prove2.me/submissions/a49383be-a3b2-4c7e-811c-8c7608c25650

import Definitions.Def_Operator_Crouzeix_ConvexRunge
import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Definitions.Def_Operator_NumericalRange_Convex
import Definitions.Def_Operator_NumericalRange_Nonempty
import Definitions.Def_Operator_Crouzeix_NormalProductSymmetrized
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_exists_polynomial_separator_of_isCompact_nonempty_convex
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polytopeRoundedSupportDomainOfRange_carrier
import Theorems.Thm_polytopeRoundedSupportDomain_boundaryParam
import Theorems.Thm_polytopeRoundedSupportDomain_carrier
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange
attribute [local simp] polytopeRoundedSupportDomainOfRange_carrier
attribute [local simp] polytopeRoundedSupportDomain_boundaryParam
attribute [local simp] polytopeRoundedSupportDomain_carrier
attribute [local simp] smoothSupportDirectionalLinearMap_apply



set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Pointwise
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    [Nontrivial E] (A : E →L[ℂ] E) {K : Set ℂ}
    (hcompact : IsCompact K) (hnonempty : K.Nonempty) (hconvex : Convex ℝ K)
    (c : ℂ) {R : ℝ}
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (A - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q K) :
    c ∈ K := by
  by_contra hc
  obtain ⟨p, r, hr0, hr1, hpc, hpK⟩ :=
    exists_polynomial_separator_of_isCompact_nonempty_convex
      K hcompact hnonempty hconvex hc
  obtain ⟨n, hrn⟩ : ∃ n : ℕ, r ^ n < (1 / 8 : ℝ) :=
    exists_pow_lt_of_lt_one (by norm_num) hr1
  let q : Polynomial ℂ := p ^ n
  let B : E →L[ℂ] E := Polynomial.aeval A q
  have hsup : polynomialSupNorm q K ≤ r ^ n := by
    unfold q polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (pow_nonneg hr0 n)
    refine Real.iSup_le (fun hz ↦ ?_) (pow_nonneg hr0 n)
    simp only [Polynomial.eval_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hpK z hz) n
  have hG : crouzeixPolynomialAuxiliaryOperator A
      (SmoothJordanDomain.ball c R
        ((norm_nonneg (A - c • 1)).trans_lt hA)) q =
      (1 : E →L[ℂ] E) := by
    rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA q]
    simp only [q, Polynomial.eval_pow, hpc, one_pow, star_one, one_smul]
  have hBadd : ‖B + (1 : E →L[ℂ] E)‖ ≤ 2 * r ^ n := by
    have h := hsymm q
    rw [hG, star_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left hsup (by norm_num))
  have hsup_sq : polynomialSupNorm (q ^ 2) K ≤ (r ^ n) ^ 2 := by
    unfold polynomialSupNorm
    refine Real.iSup_le (fun z ↦ ?_) (sq_nonneg _)
    refine Real.iSup_le (fun hz ↦ ?_) (sq_nonneg _)
    simp only [Polynomial.eval_pow, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_eval_le_polynomialSupNorm q
        (bddAbove_norm_eval_image_of_isCompact q hcompact) hz).trans hsup) 2
  have hG_sq : crouzeixPolynomialAuxiliaryOperator A
      (SmoothJordanDomain.ball c R
        ((norm_nonneg (A - c • 1)).trans_lt hA)) (q ^ 2) =
      (1 : E →L[ℂ] E) := by
    rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
      A c hA (q ^ 2)]
    simp only [q, Polynomial.eval_pow, hpc, one_pow, star_one, one_smul]
  have hBsqadd : ‖B ^ 2 + (1 : E →L[ℂ] E)‖ ≤ 2 * (r ^ n) ^ 2 := by
    have h := hsymm (q ^ 2)
    rw [hG_sq, star_one] at h
    simpa only [B, map_pow] using
      h.trans (mul_le_mul_of_nonneg_left hsup_sq (by norm_num))
  have hBsub : ‖B - (1 : E →L[ℂ] E)‖ ≤ 2 * r ^ n + 2 := by
    calc
      ‖B - (1 : E →L[ℂ] E)‖ =
          ‖(B + 1) - (2 : ℂ) • (1 : E →L[ℂ] E)‖ := by
            congr 1
            module
      _ ≤ ‖B + (1 : E →L[ℂ] E)‖ +
          ‖(2 : ℂ) • (1 : E →L[ℂ] E)‖ := norm_sub_le _ _
      _ ≤ 2 * r ^ n + 2 := by
        rw [norm_smul, norm_one]
        norm_num
        exact hBadd
  have hid : (2 : ℂ) • (1 : E →L[ℂ] E) =
      (B ^ 2 + 1) - (B + 1) * (B - 1) := by
    noncomm_ring
    module
  have htwo : (2 : ℝ) ≤
      ‖B ^ 2 + (1 : E →L[ℂ] E)‖ +
        ‖B + (1 : E →L[ℂ] E)‖ * ‖B - (1 : E →L[ℂ] E)‖ := by
    have hnormtwo : ‖(2 : ℂ) • (1 : E →L[ℂ] E)‖ = 2 := by
      rw [norm_smul, norm_one]
      norm_num
    rw [← hnormtwo, hid]
    exact (norm_sub_le _ _).trans
      (add_le_add_right (norm_mul_le (B + 1) (B - 1)) _)
  have hupper :
      ‖B ^ 2 + (1 : E →L[ℂ] E)‖ +
          ‖B + (1 : E →L[ℂ] E)‖ * ‖B - (1 : E →L[ℂ] E)‖ ≤
        2 * (r ^ n) ^ 2 + (2 * r ^ n) * (2 * r ^ n + 2) := by
    exact add_le_add hBsqadd
      (mul_le_mul hBadd hBsub (norm_nonneg _) (by positivity))
  have hrnpow : 0 ≤ r ^ n := pow_nonneg hr0 n
  nlinarith only [htwo, hupper, hrn, hrnpow]

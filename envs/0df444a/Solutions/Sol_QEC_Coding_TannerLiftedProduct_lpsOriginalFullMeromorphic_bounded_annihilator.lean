-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFullMeromorphic_bounded_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:58:14.933015+00:00
-- url     : https://prove2.me/submissions/e25d5786-edf7-484c-84c6-764256dbb886

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_exists_nested_annihilator
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphic_nested_annihilator_germ
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
    ∀ x : lpsOriginalFilledMeromorphicRestrictionSubfield N hN,
      ∃ P : Polynomial (FractionRing (Polynomial ℂ)), P.Monic ∧
        P.natDegree ≤ Nat.card (LPSOriginalMeromorphicCosets N) ∧ Polynomial.aeval x P = 0 := by
  let := (lpsOriginalFullMeromorphicJFractionEmbedding N hN).toAlgebra
  intro x
  obtain ⟨F,hF,hx⟩ := x.property
  have heq : x = lpsOriginalFilledMeromorphicRestriction N hN F hF := by
    apply Subtype.ext
    apply Subtype.ext
    exact hx
  obtain ⟨Φ,hΦ,hdeg,hroot⟩ :=
    lpsOriginalFilledMeromorphic_exists_nested_annihilator N hN F hF
  let Q := Φ.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
  have hQ : Q ≠ 0 := by
    intro hz
    apply hΦ
    apply Polynomial.map_injective (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
      (IsFractionRing.injective (Polynomial ℂ) (FractionRing (Polynomial ℂ)))
    simpa only [Polynomial.map_zero] using hz
  have hzero : Polynomial.aeval x Q = 0 := by
    rw [heq,Polynomial.aeval_def,Polynomial.eval₂_map]
    exact lpsOriginalFilledMeromorphic_nested_annihilator_germ N hN F hF Φ hroot
  refine ⟨Q * Polynomial.C (Q.leadingCoeff)⁻¹,
    Polynomial.monic_mul_leadingCoeff_inv hQ,?_,?_⟩
  · exact Polynomial.natDegree_mul_le.trans
      (by simpa only [Polynomial.natDegree_C,add_zero] using
        (Polynomial.natDegree_map_le.trans hdeg))
  · rw [map_mul,hzero,zero_mul]
end QEC.Coding.TannerLiftedProduct

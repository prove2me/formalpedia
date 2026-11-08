-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4DenominatorCosetPolynomial_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:34:22.847219+00:00
-- url     : https://prove2.me/submissions/bf6acba0-31c4-4e11-8f54-abfeca41eb78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRestrictedE4_coset
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
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        (-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N) *
          (ModularForm.E₄ τ^3)^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by
  classical
  let := Fintype.ofFinite (LPSOriginalMeromorphicCosets N)
  let B := lpsOriginalMeromorphicE4PowerAtLevel N k
  let f := fun q : LPSOriginalMeromorphicCosets N =>
    Polynomial.C (SlashInvariantForm.quotientFunc A q τ) -
      Polynomial.X * Polynomial.C (SlashInvariantForm.quotientFunc B q τ)
  have hd (q : LPSOriginalMeromorphicCosets N) (_ : q ∈ Finset.univ) :
      (f q).natDegree ≤ 1 := by
    dsimp only [f]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  have hcoef (q : LPSOriginalMeromorphicCosets N) :
      (f q).coeff 1 = -(ModularForm.E₄ τ^3)^k := by
    dsimp only [f]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_X_mul]
    simp only [one_ne_zero, if_false, Polynomial.coeff_C_zero, zero_sub]
    rw [lpsOriginalRestrictedE4_coset]
  have hc := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) f 1 hd
  change (∏ q : LPSOriginalMeromorphicCosets N, f q).coeff _ = _
  rw [Nat.card_eq_fintype_card]
  calc
    _ = ∏ q : LPSOriginalMeromorphicCosets N, (f q).coeff 1 := by
      simpa only [Finset.card_univ, mul_one] using hc
    _ = (-(ModularForm.E₄ τ^3)^k)^Fintype.card (LPSOriginalMeromorphicCosets N) := by
      simp only [hcoef, Finset.prod_const, Finset.card_univ]
    _ = _ := by rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
end QEC.Coding.TannerLiftedProduct

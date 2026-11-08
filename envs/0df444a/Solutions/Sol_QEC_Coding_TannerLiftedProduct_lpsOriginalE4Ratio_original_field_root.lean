-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalE4Ratio_original_field_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:33:34.381456+00:00
-- url     : https://prove2.me/submissions/57a318ff-4de9-41a7-b482-40e8d3663547

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicE4PowerAtLevel_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_root_at
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4PowerHolomorphic_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicFraction_root_of_pointEquations
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_degree
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)).eval₂
      ((algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom)
      ((algebraMap R H (lpsOriginalLevelFormHolomorphic N k A)) /
        (algebraMap R H (lpsOriginalE4PowerHolomorphic k))) = 0 := by
  let Φ := lpsOriginalMeromorphicRatioEquation N k A
    (lpsOriginalMeromorphicE4PowerAtLevel N k)
  let p := Φ.map lpsOriginalJHolomorphicEval.toRingHom
  have hr := lpsOriginalHolomorphicFraction_root_of_pointEquations p
    (Nat.card (LPSOriginalMeromorphicCosets N))
    (Polynomial.natDegree_map_le.trans (lpsOriginalMeromorphicRatioEquation_degree N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k)))
    (lpsOriginalLevelFormHolomorphic N k A)
    (lpsOriginalE4PowerHolomorphic k)
    (lpsOriginalE4PowerHolomorphic_ne_zero k) ?_
  · dsimp only [p] at hr
    rw [Polynomial.eval₂_map] at hr
    exact hr
  · intro τ hb
    let e := lpsOriginalHolomorphicPointEvaluation τ
    have he : e.comp lpsOriginalJHolomorphicEval.toRingHom =
        Polynomial.evalRingHom (lpsOriginalJInvariant τ) := by
      apply RingHom.ext
      intro q
      exact lpsOriginalJHolomorphicEval_apply q τ
    dsimp only [p]
    rw [Polynomial.eval₂_map, he]
    apply lpsOriginalMeromorphicRatioEquation_root_at N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ
    rw [lpsOriginalMeromorphicE4PowerAtLevel_apply,
      lpsOriginalE4PowerHolomorphic_apply]
    change A τ = (ModularForm.E₄ τ^3)^k * (A τ / (ModularForm.E₄ τ^3)^k)
    rw [mul_div_cancel₀]
    exact (lpsOriginalE4PowerHolomorphic_apply k τ) ▸ hb
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDeltaDenominatorEquation_coeff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:52:22.624205+00:00
-- url     : https://prove2.me/submissions/736210af-f9bb-4d67-9eb5-e418ac86e26d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.Algebra.Polynomial.BigOperators
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDeltaDenominatorCosetPolynomial_coeff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJPolynomialEvalHom_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_recovery


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalMeromorphicRatioEquation N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k)).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        Polynomial.C ((-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N)) := by
  apply lpsOriginalJPolynomialEvalHom_injective
  funext τ
  change Polynomial.eval (lpsOriginalJInvariant τ) _ =
    Polynomial.eval (lpsOriginalJInvariant τ) (Polynomial.C _)
  rw [Polynomial.eval_C]
  have h := congrArg (fun p : Polynomial ℂ => p.coeff (Nat.card (LPSOriginalMeromorphicCosets N)))
    (lpsOriginalMeromorphicRatioEquation_recovery N k A
      (lpsOriginalMeromorphicDeltaPowerAtLevel N k) τ)
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,
    lpsOriginalDeltaDenominatorCosetPolynomial_coeff] at h
  exact mul_left_cancel₀ (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))
    (h.trans (mul_comm _ _))
end QEC.Coding.TannerLiftedProduct

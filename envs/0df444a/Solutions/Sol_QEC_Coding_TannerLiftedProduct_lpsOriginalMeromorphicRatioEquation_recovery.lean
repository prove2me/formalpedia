-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:43:30.922071+00:00
-- url     : https://prove2.me/submissions/3811776f-fde6-44f2-97e9-f9076ee14fe4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicModularRatio
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDegreeBound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_eval
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioCosetPolynomial_degree
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioNormCoefficient_spec
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_map
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularInterpolationNodes_injective
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
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ ^
      (k*Nat.card (LPSOriginalMeromorphicCosets N))) *
        (lpsOriginalMeromorphicRatioEquation N k A B).map
          (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) =
      lpsOriginalMeromorphicRatioCosetPolynomial N k A B τ := by
  classical
  let r := Nat.card (LPSOriginalMeromorphicCosets N)
  let d := ModularForm.discriminant τ ^ (k*r)
  rw [lpsOriginalMeromorphicRatioEquation_map]
  have hm : Polynomial.C d * Lagrange.interpolate (Finset.univ : Finset (Fin (r+1)))
      (fun i => (i.val : ℂ))
      (fun i => (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval
        (lpsOriginalJInvariant τ)) =
      Lagrange.interpolate (Finset.univ : Finset (Fin (r+1))) (fun i => (i.val : ℂ))
        (fun i => d * (lpsOriginalMeromorphicRatioNormCoefficient N k A B (i.val : ℂ)).eval
          (lpsOriginalJInvariant τ)) := by
    simp only [Lagrange.interpolate_apply,Finset.mul_sum,Polynomial.C_mul,mul_assoc]
  rw [hm]
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _
    (lpsOriginalModularInterpolationNodes_injective r).injOn
  · apply Polynomial.degree_le_natDegree.trans_lt
    have hh := Nat.lt_succ_of_le
      (lpsOriginalMeromorphicRatioCosetPolynomial_degree N k A B τ)
    simp only [Finset.card_univ,Fintype.card_fin]
    exact_mod_cast hh
  · intro i hi
    rw [lpsOriginalMeromorphicRatioCosetPolynomial_eval]
    exact (lpsOriginalMeromorphicRatioNormCoefficient_spec N k A B (i.val : ℂ)).2 τ
end QEC.Coding.TannerLiftedProduct

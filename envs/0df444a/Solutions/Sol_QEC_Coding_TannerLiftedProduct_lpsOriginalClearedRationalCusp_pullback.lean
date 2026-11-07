-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:16:36.373051+00:00
-- url     : https://prove2.me/submissions/6d40894b-2327-4146-bc7d-a5dbdec4d0cd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearingBound_le
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_pullback
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_eval
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (P : Polynomial (Polynomial ℂ)) (τ : ℍ) :
    lpsOriginalClearedRationalCusp N (lpsOriginalClearingBound N P) P
      (Function.Periodic.qParam 1 (τ:ℂ))=
      (Function.Periodic.qParam 1 (τ:ℂ))^(lpsOriginalClearingBound N P)*
        (lpsOriginalRationalBivariateRetraction P).eval₂
          ((Polynomial.evalRingHom (lpsOriginalJInvariant τ)).comp
            (Polynomial.mapRingHom (algebraMap ℚ ℂ))) (lpsOriginalJDilated N hN τ) := by
  classical
  rw [lpsOriginalRationalBivariateRetraction_eval]
  simp only [lpsOriginalClearedRationalCusp,Finset.sum_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [lpsOriginalClearedMonomial_pullback N hN _ i k
    (lpsOriginalClearingBound_le N P hk hi)]
  ring
end QEC.Coding.TannerLiftedProduct

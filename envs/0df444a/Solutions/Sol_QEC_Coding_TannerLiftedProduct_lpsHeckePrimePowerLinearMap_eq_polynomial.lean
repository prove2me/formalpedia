-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckePrimePowerLinearMap_eq_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:02:52.758707+00:00
-- url     : https://prove2.me/submissions/8ce47b80-6fec-49db-925f-ed74a215b1fd

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_add_two
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
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N) (r : ℕ) :
    lpsHeckePrimePowerLinearMap N p hNp r=
      (lpsHeckePolynomial ℂ (p:ℂ) r).eval₂
        (algebraMap ℂ (Module.End ℂ (CuspForm
          (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)))
        (lpsCuspHeckeLinearMap N p hNp) := by
  induction r using Nat.twoStepInduction with
  | zero => simp only [lpsHeckePrimePowerLinearMap,lpsHeckePolynomial_zero,Polynomial.eval₂_one];rfl
  | one => simp [lpsHeckePrimePowerLinearMap]
  | more r ih0 ih1 =>
    rw [lpsHeckePrimePowerLinearMap,lpsHeckePolynomial_add_two,
      Polynomial.eval₂_sub,Polynomial.eval₂_X_mul]
    rw [Polynomial.eval₂_mul_noncomm _ _
      (fun k => Algebra.commute_algebraMap_left _ _),Polynomial.eval₂_C,←ih0,←ih1]
    rfl
end QEC.Coding.TannerLiftedProduct

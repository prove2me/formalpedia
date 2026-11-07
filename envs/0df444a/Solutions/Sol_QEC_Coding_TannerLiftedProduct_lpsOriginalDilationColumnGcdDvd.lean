-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalDilationColumnGcdDvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:16:40.695079+00:00
-- url     : https://prove2.me/submissions/f1de3790-ba7f-432b-be04-598474eabdd1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
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
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (γ : SL(2,ℤ)) :
    Int.gcd ((N:ℤ)*γ 0 0) (γ 1 0)∣N := by
  have hd : γ 0 0*γ 1 1-γ 0 1*γ 1 0=1 := by
    simpa only [Matrix.det_fin_two] using γ.det_coe
  have h := Int.dvd_add
    (dvd_mul_of_dvd_left (Int.gcd_dvd_left ((N:ℤ)*γ 0 0) (γ 1 0)) (γ 1 1))
    (dvd_mul_of_dvd_left (Int.gcd_dvd_right ((N:ℤ)*γ 0 0) (γ 1 0)) (-(N:ℤ)*γ 0 1))
  have he : (N:ℤ)*γ 0 0*γ 1 1+γ 1 0*(-(N:ℤ)*γ 0 1)=(N:ℤ) := by
    linear_combination (N:ℤ)*hd
  rw [he] at h
  exact Int.natCast_dvd_natCast.mp h
end QEC.Coding.TannerLiftedProduct

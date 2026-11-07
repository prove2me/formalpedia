-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilation_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:32.333987+00:00
-- url     : https://prove2.me/submissions/6a391d0d-01e9-4e56-a038-930e4946285d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
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
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N)
    (γ : SL(2,ℤ)) (k : ℤ) (hk : γ 1 0=(N:ℤ)*k) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) *
      lpsE2AffineMatrix N hN 0 =
      lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  have hδ : (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk) :
      Matrix (Fin 2) (Fin 2) ℝ)=!![(γ 0 0:ℝ),(N:ℝ)*(γ 0 1:ℝ);(k:ℝ),(γ 1 1:ℝ)] := by
    rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
    change (!![γ 0 0,(N:ℤ)*γ 0 1;k,γ 1 1] : Matrix (Fin 2) (Fin 2) ℤ).map
      (algebraMap ℤ ℝ)=_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map,Matrix.of_apply]
  apply Units.ext
  change (Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2DilationConjugate N γ k hk):
    Matrix (Fin 2) (Fin 2) ℝ) * (lpsE2AffineMatrix N hN 0:Matrix (Fin 2) (Fin 2) ℝ)=
    (lpsE2AffineMatrix N hN 0:Matrix (Fin 2) (Fin 2) ℝ) *
      (Matrix.SpecialLinearGroup.mapGL ℝ γ:Matrix (Fin 2) (Fin 2) ℝ)
  rw [hδ,lpsE2AffineMatrix_coe,Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.map,Matrix.of_apply,hk] <;> ring
end QEC.Coding.TannerLiftedProduct

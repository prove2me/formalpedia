-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCusp_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:36.402018+00:00
-- url     : https://prove2.me/submissions/fcaff999-2de2-4326-b7bc-7e445d8f6e00

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_slash_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
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
theorem _root_.solution (N : ℕ) (hN : 0<N) (ρ : SL(2,ℤ)) (τ : ℍ) :
    (N:ℂ)^2*(lpsOriginalJDilationCuspE4 N hN ρ τ)^3 /
      lpsOriginalJDilationCuspDelta N hN ρ τ=
      lpsOriginalJDilated N hN (Matrix.SpecialLinearGroup.mapGL ℝ ρ•τ) := by
  let M := lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ ρ
  have hd : M.det.val=(N:ℝ) := by
    change (lpsE2AffineMatrix N hN 0 * Matrix.SpecialLinearGroup.mapGL ℝ ρ).det.val=_
    rw [map_mul]
    simp only [Matrix.SpecialLinearGroup.det_mapGL,mul_one]
    exact lpsE2AffineMatrix_det N hN 0
  have hp : 0<M.det.val := by rw [hd];exact_mod_cast hN
  have he : (lpsOriginalJDilationCuspE4 N hN ρ:ℍ→ℂ)=
      (ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] M := by
    change ((ModularForm.E₄:ℍ→ℂ) ∣[(4:ℤ)] lpsE2AffineMatrix N hN 0)
      ∣[(4:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ=_
    exact (SlashAction.slash_mul _ _ _ _).symm
  have hD : (lpsOriginalJDilationCuspDelta N hN ρ:ℍ→ℂ)=
      (CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] M := by
    change ((CuspForm.discriminant:ℍ→ℂ) ∣[(12:ℤ)] lpsE2AffineMatrix N hN 0)
      ∣[(12:ℤ)] Matrix.SpecialLinearGroup.mapGL ℝ ρ=_
    exact (SlashAction.slash_mul _ _ _ _).symm
  have h := lpsOriginalJInvariant_slash_ratio M hp τ
  rw [hd] at h
  simpa only [he,hD,Complex.ofReal_natCast,M,mul_smul,lpsOriginalJDilated] using h
end QEC.Coding.TannerLiftedProduct

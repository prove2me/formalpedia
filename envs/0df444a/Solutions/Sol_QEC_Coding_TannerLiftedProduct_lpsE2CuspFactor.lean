-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2CuspFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:29.942495+00:00
-- url     : https://prove2.me/submissions/82241f1e-82b2-4f7e-b371-5db113eb671a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2CuspFactor_matrix
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [NeZero q] (r : ℤ) (g : ℝ) (hg : g≠0)
    (δ : SL(2,ℤ)) (ha : (δ 0 0:ℝ)*g=(r:ℝ)+1) (hc : (δ 1 0:ℝ)*g=(q:ℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2RealTranslation ((r:ℝ)/(q:ℝ))) *
      Matrix.SpecialLinearGroup.mapGL ℝ (lpsE2PrimeCuspMatrix q) =
      Matrix.SpecialLinearGroup.mapGL ℝ δ * Matrix.SpecialLinearGroup.mapGL ℝ
        (lpsE2DiagonalTranslation g ((δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)) hg) := by
  have hdet : (δ 0 0:ℝ)*(δ 1 1:ℝ)-(δ 0 1:ℝ)*(δ 1 0:ℝ)=1 := by
    have hd : δ 0 0*δ 1 1-δ 0 1*δ 1 0=1 := by
      simpa only [Matrix.det_fin_two] using δ.det_coe
    exact_mod_cast hd
  have hq : (q:ℝ)≠0 := by exact_mod_cast NeZero.ne q
  have hm := lpsE2CuspFactor_matrix g (q:ℝ) (r:ℝ) (δ 0 0:ℝ) (δ 0 1:ℝ)
    (δ 1 0:ℝ) (δ 1 1:ℝ) hg hq ha hc hdet
  apply Units.ext
  change ((lpsE2RealTranslation ((r:ℝ)/(q:ℝ)):Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℝ)) *
    ((lpsE2PrimeCuspMatrix q:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)) =
    ((δ:Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)) *
    ((lpsE2DiagonalTranslation g ((δ 1 1:ℝ)*(r:ℝ)/(q:ℝ)-(δ 0 1:ℝ)) hg:
      Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℝ))
  convert hm using 1
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply,lpsE2RealTranslation,lpsE2PrimeCuspMatrix,Matrix.mul_apply,
        Fin.sum_univ_two,Matrix.of_apply,add_comm]
  · congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
end QEC.Coding.TannerLiftedProduct

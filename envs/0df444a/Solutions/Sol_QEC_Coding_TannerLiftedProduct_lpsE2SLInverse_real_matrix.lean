-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2SLInverse_real_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:33.978185+00:00
-- url     : https://prove2.me/submissions/b7af7276-066b-4943-b033-f7d0c799cb01

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
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
theorem _root_.solution (δ : SL(2,ℤ)) :
    (((Matrix.SpecialLinearGroup.mapGL ℝ δ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(δ 1 1:ℝ),-(δ 0 1:ℝ);-(δ 1 0:ℝ),(δ 0 0:ℝ)] := by
  rw [← map_inv]
  change ((δ⁻¹:SL(2,ℤ)):Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)=_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map,Matrix.of_apply]
end QEC.Coding.TannerLiftedProduct

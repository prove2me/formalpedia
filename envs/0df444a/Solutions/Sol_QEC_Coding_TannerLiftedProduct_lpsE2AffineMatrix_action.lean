-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_action
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:57.151782+00:00
-- url     : https://prove2.me/submissions/13d8b386-8a3d-467d-a237-90b9b9d1f818

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_coe
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
theorem _root_.solution (m : ℕ) (hm : 0<m) (r : ℝ) (z : ℍ) :
    ((lpsE2AffineMatrix m hm r • z:ℍ):ℂ)=(m:ℂ)*(z:ℂ)+(r:ℂ) := by
  simp [UpperHalfPlane.coe_smul,UpperHalfPlane.σ,hm,UpperHalfPlane.num,UpperHalfPlane.denom,
    lpsE2AffineMatrix_coe,Matrix.of_apply]
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2AffineMatrix_qParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:13:09.972601+00:00
-- url     : https://prove2.me/submissions/b065eb6b-a1ab-4913-823f-27f38bb36946

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_action
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
theorem _root_.solution (m : ℕ) (hm : 0 < m) (z : ℍ) :
    Function.Periodic.qParam 1 ((lpsE2AffineMatrix m hm 0 • z:ℍ):ℂ)=
      Function.Periodic.qParam 1 (z:ℂ)^m := by
  rw [lpsE2AffineMatrix_action]
  simp only [Function.Periodic.qParam,Complex.ofReal_one,div_one,Complex.ofReal_zero,add_zero]
  rw [show 2*Real.pi*I*((m:ℂ)*(z:ℂ))=(m:ℂ)*(2*Real.pi*I*(z:ℂ)) by ring]
  exact Complex.exp_nat_mul _ m
end QEC.Coding.TannerLiftedProduct

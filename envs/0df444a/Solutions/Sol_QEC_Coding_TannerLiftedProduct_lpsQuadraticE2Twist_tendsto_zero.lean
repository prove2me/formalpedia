-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:04.740208+00:00
-- url     : https://prove2.me/submissions/28f26d2c-517d-4c87-804e-33665e3aebce

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFunction_periodic_comp_ofComplex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_coeff_qExpansion
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_isBoundedAtImInfty
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_mdifferentiable
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    Tendsto (lpsQuadraticE2Twist q) UpperHalfPlane.atImInfty (𝓝 0) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsQuadraticE2Twist_add_one q)
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp
    (lpsQuadraticE2Twist_mdifferentiable q) (lpsQuadraticE2Twist_isBoundedAtImInfty q hq2)
  have hc : UpperHalfPlane.cuspFunction 1 (lpsQuadraticE2Twist q) 0=0 := by
    have h := lpsQuadraticE2Twist_coeff_qExpansion q hq2 0
    simpa [UpperHalfPlane.qExpansion_coeff,MulChar.map_zero] using h
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 (lpsQuadraticE2Twist q)
      (Function.Periodic.qParam 1 (z:ℂ)))=lpsQuadraticE2Twist q := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h
end QEC.Coding.TannerLiftedProduct

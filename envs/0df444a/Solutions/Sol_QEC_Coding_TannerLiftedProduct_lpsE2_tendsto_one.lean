-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsE2_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:17.599403+00:00
-- url     : https://prove2.me/submissions/27a3459f-6ce2-4c41-be92-f0e46b7cfd57

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFunction_periodic_comp_ofComplex
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
theorem _root_.solution : Tendsto EisensteinSeries.E2 UpperHalfPlane.atImInfty (𝓝 1) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ lpsE2_add_one
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1)
    hp E2_mdifferentiable EisensteinSeries.isBoundedAtImInfty_E2
  let f : C(ℍ,ℂ) := ⟨EisensteinSeries.E2,E2_mdifferentiable.continuous⟩
  have hcoeff := UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [Function.Periodic.qParam,Complex.ofReal_one,div_one,f,
      ContinuousMap.coe_mk] using EisensteinSeries.hasSum_qExpansion_E2 (z:=z)) 0
  have hc : UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2 0=1 := by
    simpa [UpperHalfPlane.qExpansion_coeff,f] using hcoeff.symm
  have he : (fun z : ℍ => UpperHalfPlane.cuspFunction 1 EisensteinSeries.E2
      (Function.Periodic.qParam 1 (z:ℂ)))=EisensteinSeries.E2 := by
    funext z
    exact UpperHalfPlane.eq_cuspFunction z (by norm_num) hp
  have h := ha.continuousAt.tendsto.comp
    (UpperHalfPlane.qParam_tendsto_atImInfty (by norm_num : (0:ℝ)<1))
  simpa only [Function.comp_def,hc,he] using h
end QEC.Coding.TannerLiftedProduct

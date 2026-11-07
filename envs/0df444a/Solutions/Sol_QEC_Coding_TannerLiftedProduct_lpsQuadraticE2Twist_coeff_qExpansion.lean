-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_coeff_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:57:33.774449+00:00
-- url     : https://prove2.me/submissions/54b7212a-87e3-4ed7-9c90-45251122871d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGaussEvaluation
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_mdifferentiable
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_isBoundedAtImInfty
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Twist_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFunction_periodic_comp_ofComplex
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsQuadraticE2Twist q z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsQuadraticE2Character q (n:ZMod q) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsQuadraticE2Twist_add_one q)
  have hm := lpsQuadraticE2Twist_mdifferentiable q
  have hb := lpsQuadraticE2Twist_isBoundedAtImInfty q hq2
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hm hb
  let f : C(ℍ,ℂ) := ⟨fun z => lpsQuadraticE2Twist q z,hm.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using lpsQuadraticE2Twist_hasSum q hq2 z) n
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_coeff_qExpansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:21.370607+00:00
-- url     : https://prove2.me/submissions/8fddedbe-c5dc-4732-aeb6-a1423b14637d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_hasSum
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_isBoundedAtImInfty
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_add_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
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
theorem _root_.solution (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (fun z : ℍ => lpsChi4E2Twist z)) =
      -24*(ArithmeticFunction.sigma 1 n:ℂ)*lpsChi4E2Character (n:ZMod 4) := by
  have hp := lpsFunction_periodic_comp_ofComplex _ (lpsChi4E2Twist_add_one)
  have hm := lpsChi4E2Twist_mdifferentiable
  have hb := lpsChi4E2Twist_isBoundedAtImInfty
  have ha := UpperHalfPlane.analyticAt_cuspFunction_zero (by norm_num : (0:ℝ)<1) hp hm hb
  let f : C(ℍ,ℂ) := ⟨fun z => lpsChi4E2Twist z,hm.continuous⟩
  symm
  exact UpperHalfPlane.qExpansion_coeff_unique f (by norm_num : (0:ℝ)<1) ha
    (fun z => by simpa only [smul_eq_mul,f,ContinuousMap.coe_mk] using lpsChi4E2Twist_hasSum z) n
end QEC.Coding.TannerLiftedProduct

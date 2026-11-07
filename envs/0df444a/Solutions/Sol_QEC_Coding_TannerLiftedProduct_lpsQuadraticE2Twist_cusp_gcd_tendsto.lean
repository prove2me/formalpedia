-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Twist_cusp_gcd_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:55:36.949593+00:00
-- url     : https://prove2.me/submissions/aa4c9e3f-03dc-4f00-93fc-31dfcd7194e8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_cusp_tendsto
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Dilate_one
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
theorem _root_.solution (q : ℕ) [Fact q.Prime] (γ : SL(2,ℤ)) :
    Tendsto (lpsQuadraticE2Twist q ∣[(2:ℤ)] γ) UpperHalfPlane.atImInfty
      (𝓝 ((gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q)))⁻¹ *
        ∑ r : Fin q,lpsQuadraticE2Character q (r.val:ZMod q)*
          (((Int.gcd ((q:ℤ)*γ 0 0+(r.val:ℤ)*γ 1 0)
            ((q:ℤ)*γ 1 0):ℕ):ℂ)^2/(q:ℂ)^2))) := by
  simpa only [lpsQuadraticE2Dilate_one,Nat.cast_one,Int.cast_one,mul_one,one_pow] using
    lpsQuadraticE2Dilate_cusp_tendsto q 1 (by decide) γ
end QEC.Coding.TannerLiftedProduct

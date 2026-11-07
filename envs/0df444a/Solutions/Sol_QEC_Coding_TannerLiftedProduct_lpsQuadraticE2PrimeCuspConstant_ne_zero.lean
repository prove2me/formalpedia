-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2PrimeCuspConstant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:23.879532+00:00
-- url     : https://prove2.me/submissions/5eb53b4c-7235-494e-b33e-20f6e0498fde

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCusps
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Gauss_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq2 : q≠2) :
    lpsQuadraticE2Character q (-1:ZMod q)*((q:ℂ)^2-1)/
      gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))≠0 := by
  have hc : lpsQuadraticE2Character q (-1:ZMod q)≠0 :=
    (IsUnit.map (lpsQuadraticE2Character q) isUnit_neg_one).ne_zero
  have hq : (1:ℝ)<(q:ℝ) := by exact_mod_cast (Fact.out : q.Prime).one_lt
  have hq' : (q:ℝ)^2-1≠0 := by nlinarith
  have hn : (q:ℂ)^2-1≠0 := by exact_mod_cast hq'
  exact div_ne_zero (mul_ne_zero hc hn) (lpsQuadraticE2Gauss_ne_zero q hq2)
end QEC.Coding.TannerLiftedProduct

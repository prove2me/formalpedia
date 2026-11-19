-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Character_neg_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:42:09.804006+00:00
-- url     : https://prove2.me/submissions/03826f53-7b71-46d0-949c-180f854fbab9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaEisensteinCusps
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_neg_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (A D : ZMod q) : lpsQuadraticE2Character q (-A/D)=lpsQuadraticE2Character q (A*D) := by
  have hχ : (lpsQuadraticE2Character q).IsQuadratic :=
    (quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)
  rw [div_eq_mul_inv,neg_eq_neg_one_mul,map_mul,map_mul,
    lpsQuadraticE2Character_neg_one q hq4,one_mul,←MulChar.inv_apply',hχ.inv,map_mul]
end QEC.Coding.TannerLiftedProduct

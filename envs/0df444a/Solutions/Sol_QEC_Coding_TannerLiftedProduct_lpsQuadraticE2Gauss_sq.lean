-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsQuadraticE2Gauss_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:39:07.385477+00:00
-- url     : https://prove2.me/submissions/369a0d2d-9bf7-4718-a274-b0c089159397

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_neg_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2Character_ne_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    gaussSum (lpsQuadraticE2Character q) (ZMod.stdAddChar (N:=q))^2=(q:ℂ) := by
  have hq2 : q≠2 := by intro h;subst q;norm_num at hq4
  have h := gaussSum_sq (lpsQuadraticE2Character_ne_one q hq2)
    ((quadraticChar_isQuadratic (ZMod q)).comp (Int.castRingHom ℂ)) (ZMod.isPrimitive_stdAddChar q)
  rw [ZMod.card,lpsQuadraticE2Character_neg_one q hq4,one_mul] at h
  exact h
end QEC.Coding.TannerLiftedProduct

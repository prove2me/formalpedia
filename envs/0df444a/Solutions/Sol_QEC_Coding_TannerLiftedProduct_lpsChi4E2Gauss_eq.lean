-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:14:16.80752+00:00
-- url     : https://prove2.me/submissions/77e4b073-6f98-4499-bad2-04755f2c4951

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4Phase_three
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsFin_cast_finEquiv
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
theorem _root_.solution : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))=
    2*ZMod.stdAddChar (1:ZMod 4) := by
  have hs := (ZMod.finEquiv 4).sum_comp (fun a : ZMod 4 =>
    lpsChi4E2Character a*ZMod.stdAddChar a)
  rw [gaussSum,←hs]
  change (∑ a : Fin 4,lpsChi4E2Character (ZMod.finEquiv 4 a)*ZMod.stdAddChar (ZMod.finEquiv 4 a))=_
  simp only [←lpsFin_cast_finEquiv]
  rw [Fin.sum_univ_four]
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply,lpsChi4Phase_three]
  ring
end QEC.Coding.TannerLiftedProduct

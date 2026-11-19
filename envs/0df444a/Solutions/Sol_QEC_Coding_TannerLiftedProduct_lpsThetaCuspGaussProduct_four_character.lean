-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaCuspGaussProduct_four_character
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:41:42.491872+00:00
-- url     : https://prove2.me/submissions/83544aaa-d944-48dc-b74d-cee99f472411

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaCuspGaussProduct_four
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4UnitPhase
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsUnaryQuadraticGauss_four


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) (a : ℤ)
    (ha : IsUnit (a:ZMod 4)) :
    lpsThetaCuspGaussProduct q a 4=16*(8+4*
      gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character (a:ZMod 4)) := by
  rw [lpsThetaCuspGaussProduct_four,lpsUnaryQuadraticGauss_four]
  have h := lpsChi4UnitPhase (a:ZMod 4) ha
  linear_combination 64*h
end QEC.Coding.TannerLiftedProduct

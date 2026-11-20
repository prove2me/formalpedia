-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:13.735537+00:00
-- url     : https://prove2.me/submissions/f29ff2e0-d730-4060-9cfa-1d8a438bb53c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaSquareCoeff q hq4 0=0 :=
  lpsWeightTwoCusp_squareCoeff_zero _ _
end QEC.Coding.TannerLiftedProduct

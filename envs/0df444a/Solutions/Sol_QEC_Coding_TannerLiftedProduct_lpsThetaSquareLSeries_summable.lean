-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareLSeries_summable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:29.537176+00:00
-- url     : https://prove2.me/submissions/f9ccbdd2-9392-4bd4-932c-f13e192a0516

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareLSeries_summable


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsWeightTwoCusp_squareLSeries_summable _ _ _ hs
end QEC.Coding.TannerLiftedProduct

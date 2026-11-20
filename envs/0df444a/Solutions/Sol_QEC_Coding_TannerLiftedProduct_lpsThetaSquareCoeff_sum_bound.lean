-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:32:26.199178+00:00
-- url     : https://prove2.me/submissions/c2fe92f6-4159-4957-ad17-62d409196eed

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_coeff_square_sum_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, lpsThetaSquareCoeff q hq4 n)≤C*(X:ℝ)^2 := by
  have : NeZero ((4*q)^2) := ⟨by have hq := (Fact.out : q.Prime).pos;positivity⟩
  exact lpsWeightTwoCusp_coeff_square_sum_bound _ _
end QEC.Coding.TannerLiftedProduct

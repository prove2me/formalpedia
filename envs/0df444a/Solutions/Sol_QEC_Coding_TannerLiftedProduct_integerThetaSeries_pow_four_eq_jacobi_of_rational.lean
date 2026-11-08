-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.integerThetaSeries_pow_four_eq_jacobi_of_rational
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:25:03.454203+00:00
-- url     : https://prove2.me/submissions/04c74347-2965-4e49-9654-50ec4ec26c2d

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiLambertSeries_eq_rationalJacobiFourSquareSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (h : rationalIntegerThetaSeries ^ 4 = jacobiLambertSeries) :
    integerThetaSeries ^ 4 = jacobiFourSquareSeries := by
  apply PowerSeries.map_injective (Nat.castRingHom ℚ) Nat.cast_injective
  rw [map_pow]
  change rationalIntegerThetaSeries ^ 4 = rationalJacobiFourSquareSeries
  exact h.trans jacobiLambertSeries_eq_rationalJacobiFourSquareSeries
end QEC.Coding.TannerLiftedProduct

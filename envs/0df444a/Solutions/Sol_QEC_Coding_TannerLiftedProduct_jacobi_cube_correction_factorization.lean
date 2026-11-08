-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobi_cube_correction_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:24:54.775063+00:00
-- url     : https://prove2.me/submissions/adccd6bd-533c-4dd1-9edd-d534e9050861

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiThetaTriangular_wronskian

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    jacobiThetaProduct * jacobiTriangularProduct +
        PowerSeries.C 4 * PowerSeries.X *
          (jacobiThetaProduct *
              PowerSeries.derivative ℚ jacobiTriangularProduct -
            PowerSeries.derivative ℚ jacobiThetaProduct *
              jacobiTriangularProduct) =
      (jacobiThetaProduct * jacobiTriangularProduct) *
        (1 + PowerSeries.C 4 * PowerSeries.X *
          jacobiLogDerivativeDifference) := by
  rw [jacobiThetaTriangular_wronskian]
  ring
end QEC.Coding.TannerLiftedProduct

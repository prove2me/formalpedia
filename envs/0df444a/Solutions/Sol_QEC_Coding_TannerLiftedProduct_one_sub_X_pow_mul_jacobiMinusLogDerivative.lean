-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.one_sub_X_pow_mul_jacobiMinusLogDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:35:39.184703+00:00
-- url     : https://prove2.me/submissions/c0fb0561-31f2-49e9-8a3e-d764a674502e

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub_X_pow
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_derivative_one_sub_X_pow


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {d : ℕ} (hd : d ≠ 0) :
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) * jacobiMinusLogDerivative d =
      PowerSeries.derivative ℚ
        ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) := by
  rw [derivative_one_sub_X_pow, jacobiMinusLogDerivative]
  have hinv := jacobiGeometricSeries_subst_mul_one_sub_X_pow hd
  calc
    ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) *
        -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (PowerSeries.X ^ d)) =
      -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
        (jacobiGeometricSeries.subst (PowerSeries.X ^ d) *
          ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d))) := by ring
    _ = -(PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1)) := by
      rw [hinv]
      ring
end QEC.Coding.TannerLiftedProduct

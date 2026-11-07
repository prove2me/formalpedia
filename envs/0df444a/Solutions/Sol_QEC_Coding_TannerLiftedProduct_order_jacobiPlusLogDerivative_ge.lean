-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.order_jacobiPlusLogDerivative_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:24:57.679863+00:00
-- url     : https://prove2.me/submissions/654e7337-3d23-4cef-aa78-76ba44559918

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d : ℕ) :
    (d - 1 : ℕ∞) ≤ (jacobiPlusLogDerivative d).order := by
  rw [jacobiPlusLogDerivative]
  have hreorder :
      PowerSeries.C (d : ℚ) * PowerSeries.X ^ (d - 1) *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d)) =
        PowerSeries.X ^ (d - 1) *
          (PowerSeries.C (d : ℚ) *
            jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))) := by ring
  rw [hreorder]
  calc
    (d - 1 : ℕ∞) = (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order :=
      (PowerSeries.order_X_pow (R := ℚ) (d - 1)).symm
    _ =
        (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order + 0 := (add_zero _).symm
    _ ≤ (PowerSeries.X ^ (d - 1) : ℚ⟦X⟧).order +
        (PowerSeries.C (d : ℚ) *
          jacobiGeometricSeries.subst (-(PowerSeries.X ^ d))).order :=
      by
        gcongr
        exact bot_le
    _ ≤ _ := PowerSeries.le_order_mul _ _
end QEC.Coding.TannerLiftedProduct

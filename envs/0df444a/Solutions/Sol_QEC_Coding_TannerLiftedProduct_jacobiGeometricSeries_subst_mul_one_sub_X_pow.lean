-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.jacobiGeometricSeries_subst_mul_one_sub_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:34:36.469578+00:00
-- url     : https://prove2.me/submissions/25ce3bcd-1703-407b-baa3-c593f146791d

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_jacobiGeometricSeries_subst_mul_one_sub

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {d : ℕ} (hd : d ≠ 0) :
    (jacobiGeometricSeries.subst (PowerSeries.X ^ d)) *
      ((1 : ℚ⟦X⟧) - PowerSeries.X ^ d) = 1 :=
  jacobiGeometricSeries_subst_mul_one_sub
    (PowerSeries.HasSubst.X_pow hd)
end QEC.Coding.TannerLiftedProduct

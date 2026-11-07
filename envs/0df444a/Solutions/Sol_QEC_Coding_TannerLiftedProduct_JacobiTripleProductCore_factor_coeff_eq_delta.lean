-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.factor_coeff_eq_delta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:22:50.781268+00:00
-- url     : https://prove2.me/submissions/5d18b9ca-e6ee-447d-85ee-21be2d943115

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
namespace QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
theorem _root_.solution (m d : ℕ) (hd : m + 2 ≤ d) (j : ℕ) (hj : j ≤ m) :
    ((1 - (q : R) ^ (2 * d)) : R).coeff j = if j = 0 then 1 else 0 := by
  have h1 : ((q : R) ^ (2 * d)).coeff j = 0 := by
    have : j < 2 * d := by nlinarith
    grind only [coeff_X_pow]
  simp_all
end QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore

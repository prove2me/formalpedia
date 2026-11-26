-- Prove2me | solution 1 for SmoothJordanDomain.translate_boundaryParam_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:05.16416+00:00
-- url     : https://prove2.me/submissions/59c60fd9-58cf-4dd6-b7f5-2e9165e0e2b4

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (Omega : SmoothJordanDomain)
    (c : ℂ) (t : ℝ) :
    deriv (Omega.translate c).boundaryParam t =
      deriv Omega.boundaryParam t := by
  exact deriv_const_add_boundaryParam Omega c t
end SmoothJordanDomain

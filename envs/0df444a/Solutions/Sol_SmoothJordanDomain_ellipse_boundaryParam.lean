-- Prove2me | solution 1 for SmoothJordanDomain.ellipse_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:50.233189+00:00
-- url     : https://prove2.me/submissions/7665e8a2-b55f-417d-bec5-42ead61b984d

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (c : ℂ) (e : ℂ ≃L[ℝ] ℂ)
    (R : ℝ) (hR : 0 < R) :
    (ellipse c e R hR).boundaryParam =
      fun t => c + e (circleMap 0 R t) := rfl
end SmoothJordanDomain

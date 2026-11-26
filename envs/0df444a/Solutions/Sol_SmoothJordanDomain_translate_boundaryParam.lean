-- Prove2me | solution 1 for SmoothJordanDomain.translate_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:39.712161+00:00
-- url     : https://prove2.me/submissions/29167d1c-687d-473a-ad8f-443d31fb1bca

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).boundaryParam = fun t => c + Omega.boundaryParam t := rfl
end SmoothJordanDomain

-- Prove2me | solution 1 for SmoothJordanDomain.translate_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:33.88262+00:00
-- url     : https://prove2.me/submissions/eeeaa8d0-a504-44e9-b3e1-ecef970a974b

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (Omega : SmoothJordanDomain) (c : ℂ) :
    (Omega.translate c).carrier = (fun z => c + z) '' Omega.carrier := rfl
end SmoothJordanDomain

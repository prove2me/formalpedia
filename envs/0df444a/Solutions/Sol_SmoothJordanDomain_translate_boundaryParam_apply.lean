-- Prove2me | solution 1 for SmoothJordanDomain.translate_boundaryParam_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:41.111305+00:00
-- url     : https://prove2.me/submissions/43b5d70a-934a-4cc3-957d-d6aa2ea55fae

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
    (Omega.translate c).boundaryParam t = c + Omega.boundaryParam t := rfl
end SmoothJordanDomain

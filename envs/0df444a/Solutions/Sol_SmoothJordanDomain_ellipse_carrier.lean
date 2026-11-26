-- Prove2me | solution 1 for SmoothJordanDomain.ellipse_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:45.346875+00:00
-- url     : https://prove2.me/submissions/ac0d285c-4caf-484d-a2d2-cdbfda6b4a2c

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
    (ellipse c e R hR).carrier =
      (fun z => c + z) '' (e '' Metric.ball 0 R) := rfl
end SmoothJordanDomain

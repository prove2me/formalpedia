-- Prove2me | solution 1 for SmoothJordanDomain.ellipse_boundaryParam_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:57.346393+00:00
-- url     : https://prove2.me/submissions/620a4f7e-5898-405d-b93c-ffd2fb52f03d

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_deriv

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
open SmoothJordanDomain
namespace SmoothJordanDomain
theorem _root_.solution (c : ℂ)
    (e : ℂ ≃L[ℝ] ℂ) (R : ℝ) (hR : 0 < R) (t : ℝ) :
    deriv (ellipse c e R hR).boundaryParam t =
      e (circleMap 0 R t * I) := by
  unfold ellipse
  rw [translate_boundaryParam_deriv, linearImage_boundaryParam_deriv]
  change e (deriv (circleMap 0 R) t) = e (circleMap 0 R t * I)
  rw [deriv_circleMap]
end SmoothJordanDomain

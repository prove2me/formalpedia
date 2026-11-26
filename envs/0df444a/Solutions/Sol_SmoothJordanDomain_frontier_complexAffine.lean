-- Prove2me | solution 1 for SmoothJordanDomain.frontier_complexAffine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:03:49.135657+00:00
-- url     : https://prove2.me/submissions/99a3759f-b563-4461-bce9-956967ec0817

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped Interval Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a b : ℂ) (ha : a ≠ 0) :
    frontier (Omega.complexAffine a b ha).carrier =
      (fun z => a * z + b) '' frontier Omega.carrier := by
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  change frontier (e '' Omega.carrier) = e '' frontier Omega.carrier
  exact (e.image_frontier Omega.carrier).symm
end SmoothJordanDomain

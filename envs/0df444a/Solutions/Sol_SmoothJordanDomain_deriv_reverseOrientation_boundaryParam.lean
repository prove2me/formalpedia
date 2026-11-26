-- Prove2me | solution 1 for SmoothJordanDomain.deriv_reverseOrientation_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:45:16.502708+00:00
-- url     : https://prove2.me/submissions/ac105865-3b9f-4f3d-bd30-f4eef2e0ab5e

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport

set_option autoImplicit false
open Complex Set
open scoped Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (t : ℝ) :
    deriv Omega.reverseOrientation.boundaryParam t =
      -deriv Omega.boundaryParam (2 * Real.pi - t) := by
  exact deriv_comp_const_sub Omega.boundaryParam (2 * Real.pi) t
end SmoothJordanDomain

-- Prove2me | solution 1 for SmoothJordanDomain.reverseOrientation_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:33:40.404014+00:00
-- url     : https://prove2.me/submissions/72b5c1a3-f28f-42f2-acb4-6b40c991249b

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
    Omega.reverseOrientation.boundaryParam t =
      Omega.boundaryParam (2 * Real.pi - t) := rfl
end SmoothJordanDomain

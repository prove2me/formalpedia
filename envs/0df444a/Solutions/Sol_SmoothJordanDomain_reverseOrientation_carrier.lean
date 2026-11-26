-- Prove2me | solution 1 for SmoothJordanDomain.reverseOrientation_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:32:41.868837+00:00
-- url     : https://prove2.me/submissions/9e8b11d8-24ad-43ef-adae-47fa18f764ab

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
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.carrier = Omega.carrier := rfl
end SmoothJordanDomain

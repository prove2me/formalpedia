-- Prove2me | solution 1 for SmoothJordanDomain.canonicalOrientation_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:00.01695+00:00
-- url     : https://prove2.me/submissions/5839f765-ef05-4072-bc2b-e5df52e189fd

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
    Omega.canonicalOrientation.carrier = Omega.carrier := by
  unfold SmoothJordanDomain.canonicalOrientation
  split <;> rfl
end SmoothJordanDomain

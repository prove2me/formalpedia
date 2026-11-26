-- Prove2me | solution 1 for SmoothJordanDomain.frontier_support_of_support_at_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:25.795701+00:00
-- url     : https://prove2.me/submissions/607ebd01-4a23-4c09-8ac8-9d2893e42a68

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Theorems.Thm_SmoothJordanDomain_closure_support_and_carrier_strict_of_support_at_mem_carrier

set_option autoImplicit false
open Complex Set
open scoped Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ xi ∈ frontier Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0 := by
  intro xi hxi
  exact
    (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
      c hc t hcside).1 xi (frontier_subset_closure hxi)
end SmoothJordanDomain

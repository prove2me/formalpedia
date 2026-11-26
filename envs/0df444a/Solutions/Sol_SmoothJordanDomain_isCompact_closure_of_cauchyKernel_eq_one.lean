-- Prove2me | solution 1 for SmoothJordanDomain.isCompact_closure_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:36.477648+00:00
-- url     : https://prove2.me/submissions/610956a9-6f9e-48a3-80b3-e338e56f498c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    IsCompact (closure Omega.carrier) :=
  (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel).isCompact_closure
end SmoothJordanDomain

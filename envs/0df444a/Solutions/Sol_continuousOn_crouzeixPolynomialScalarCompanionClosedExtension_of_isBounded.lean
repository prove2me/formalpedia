-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:35.727671+00:00
-- url     : https://prove2.me/submissions/920204d4-579b-4103-9ee3-d00384233a4c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      Omega p hkernel
  intro xi hxi
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p hbounded hkernel hxi

-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionBoundaryValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:11.479623+00:00
-- url     : https://prove2.me/submissions/160da8d8-fbba-4b1b-99ee-b2f917f66c1c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionRegularized_self

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
      (frontier Omega.carrier) := by
  intro xi hxi
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  exact (p.continuous.comp continuous_id).star.continuousWithinAt.add
    (continuousOn_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi hxi)

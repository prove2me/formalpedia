-- Prove2me | solution 1 for analyticOn_crouzeixPolynomialScalarCompanion_frontier_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:43.254617+00:00
-- url     : https://prove2.me/submissions/bc4abfa9-b8b6-46f1-ab96-e14d8b58d7aa

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      (frontier Omega.carrier)ᶜ := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact
      (hasDerivAt_crouzeixPolynomialScalarCompanion_of_not_mem_frontier
        Omega p hz).differentiableAt.differentiableWithinAt
  · exact isClosed_frontier.isOpen_compl

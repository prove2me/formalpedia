-- Prove2me | solution 1 for analyticOn_crouzeixPolynomialScalarCompanion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:30.337134+00:00
-- url     : https://prove2.me/submissions/b7d84cb7-c7c2-4f7b-a7cc-8915dc7090ad

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    AnalyticOn ℂ (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier := by
  rw [analyticOn_iff_differentiableOn]
  · intro z hz
    exact (hasDerivAt_crouzeixPolynomialScalarCompanion Omega p hz).differentiableAt.differentiableWithinAt
  · exact Omega.isOpen_carrier

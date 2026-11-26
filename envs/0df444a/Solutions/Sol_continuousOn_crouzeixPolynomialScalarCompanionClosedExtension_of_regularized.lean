-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:23.674195+00:00
-- url     : https://prove2.me/submissions/f285e7b1-1b85-4671-aff9-b3b1a019fc83

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_regularized
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1)
    (hreg : ∀ xi ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        (nhdsWithin xi Omega.carrier)
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by
  apply continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
    Omega p (crouzeixPolynomialScalarCompanionBoundaryValue Omega p)
  intro xi hxi
  exact tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    Omega p hkernel xi (hreg xi hxi)

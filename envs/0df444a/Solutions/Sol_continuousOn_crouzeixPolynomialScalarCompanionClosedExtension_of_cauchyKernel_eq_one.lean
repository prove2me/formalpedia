-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:47.267827+00:00
-- url     : https://prove2.me/submissions/0b6116fd-6626-478d-ac41-67bf67bb7bac

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
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
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
      Omega p hkernel hxi

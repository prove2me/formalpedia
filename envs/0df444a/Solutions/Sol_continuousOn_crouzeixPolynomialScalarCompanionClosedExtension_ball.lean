-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:29.048641+00:00
-- url     : https://prove2.me/submissions/ab5aa319-6b18-4943-8b61-d6a41182dbcc

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p)
      (Metric.closedBall (0 : ℂ) R) := by
  have hcont :=
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      (SmoothJordanDomain.ball 0 R hR) p
      (fun z hz ↦ crouzeixScalarCauchyKernel_ball_eq_one hR hz)
      (fun xi hxi ↦ by
        apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball hR p
        change xi ∈ frontier (Metric.ball (0 : ℂ) R) at hxi
        rwa [frontier_ball 0 hR.ne'] at hxi)
  rw [show (SmoothJordanDomain.ball 0 R hR).carrier =
      Metric.ball (0 : ℂ) R by rfl,
    closure_ball 0 hR.ne'] at hcont
  exact hcont

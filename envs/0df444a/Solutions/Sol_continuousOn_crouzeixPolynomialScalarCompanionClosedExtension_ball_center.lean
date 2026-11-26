-- Prove2me | solution 1 for continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:44.504016+00:00
-- url     : https://prove2.me/submissions/fdfc793c-6d83-4649-b437-01d57b71b86c

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_center_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p)
      (Metric.closedBall c R) := by
  have hcont :=
    continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_regularized
      (SmoothJordanDomain.ball c R hR) p
      (fun z hz ↦ crouzeixScalarCauchyKernel_ball_center_eq_one c hR hz)
      (fun xi hxi ↦ by
        apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
          c hR p
        change xi ∈ frontier (Metric.ball c R) at hxi
        rwa [frontier_ball c hR.ne'] at hxi)
  rw [show (SmoothJordanDomain.ball c R hR).carrier =
      Metric.ball c R by rfl, closure_ball c hR.ne'] at hcont
  exact hcont

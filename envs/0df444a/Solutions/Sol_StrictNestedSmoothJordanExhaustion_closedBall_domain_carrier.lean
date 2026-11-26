-- Prove2me | solution 1 for StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:46.51578+00:00
-- url     : https://prove2.me/submissions/9bcfc005-baa1-4155-a78f-b567989549e5

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
namespace StrictNestedSmoothJordanExhaustion
theorem _root_.solution
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).carrier =
      Metric.ball c (smoothApproxRadius n + R) := by
  rfl
end StrictNestedSmoothJordanExhaustion

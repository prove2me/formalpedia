-- Prove2me | solution 1 for StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:01.652135+00:00
-- url     : https://prove2.me/submissions/28971429-d17e-4ef3-9386-461f3ecad802

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
    ((StrictNestedSmoothJordanExhaustion.closedBall c R hR).domain n).boundaryParam =
      circleMap c (smoothApproxRadius n + R) := by
  rfl
end StrictNestedSmoothJordanExhaustion

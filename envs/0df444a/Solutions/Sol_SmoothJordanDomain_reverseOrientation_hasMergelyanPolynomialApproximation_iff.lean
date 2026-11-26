-- Prove2me | solution 1 for SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:08.067728+00:00
-- url     : https://prove2.me/submissions/b668ab7c-83d1-4a82-9530-4bca5f2eee04

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
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by
  exact ⟨fun h => h, fun h => h⟩
end SmoothJordanDomain

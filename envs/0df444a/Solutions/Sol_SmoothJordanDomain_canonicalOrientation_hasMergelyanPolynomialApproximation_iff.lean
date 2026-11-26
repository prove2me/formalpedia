-- Prove2me | solution 1 for SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:29.921116+00:00
-- url     : https://prove2.me/submissions/707283da-c413-4838-9334-8b821bb3111f

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
namespace SmoothJordanDomain
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    Omega.canonicalOrientation.HasMergelyanPolynomialApproximation ↔
      Omega.HasMergelyanPolynomialApproximation := by
  unfold SmoothJordanDomain.HasMergelyanPolynomialApproximation
  rw [SmoothJordanDomain.canonicalOrientation_carrier]
end SmoothJordanDomain

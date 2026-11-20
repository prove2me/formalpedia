-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsThetaRankinMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T07:40:04.134651+00:00
-- url     : https://prove2.me/submissions/b5c3d40b-2d39-4953-a1c5-f11b34ee172c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_nonneg

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    0≤lpsThetaRankinMass q hq4 :=
  integral_nonneg (lpsThetaRankinDensity_nonneg q hq4)
end QEC.Coding.TannerLiftedProduct

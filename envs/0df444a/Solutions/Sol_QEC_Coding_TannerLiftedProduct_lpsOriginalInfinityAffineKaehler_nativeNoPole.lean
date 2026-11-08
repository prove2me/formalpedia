-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityAffineKaehler_nativeNoPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:03:01.447011+00:00
-- url     : https://prove2.me/submissions/d5b7b878-c7ad-45b1-9ab0-eb072f987c5c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_le_heightOne
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehlerRange_iff_nativeNoPole


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary016
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalInfinityAffineDifferentialsDictionary024
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹)
    (omega : KaehlerDifferential ℂ K)
    (h : omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range) :
    0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  apply (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mp
  exact kaehler_field_map_range_le_heightOne ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega h
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_localClear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:02:59.663023+00:00
-- url     : https://prove2.me/submissions/1d7f2fb3-2377-46d3-a9ba-f9bbaabb935c

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroPointCoverage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_range_heightOne_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehlerRange_iff_nativeNoPole


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary016
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalZeroAffineDifferentialsDictionary024
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (omega : KaehlerDifferential ℂ K)
    (h : 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
      (lpsOriginalNativeCovectorToLocal N hN x
        (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega))) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      s • omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range := by
  have hv := (lpsOriginalLocalKaehlerRange_iff_nativeNoPole N hpos hN x omega).mpr h
  exact kaehler_field_map_range_heightOne_clear ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl) omega hv
end QEC.Coding.TannerLiftedProduct

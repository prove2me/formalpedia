-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityAffineKaehlerRange_iff_nativeNoPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:18:57.876041+00:00
-- url     : https://prove2.me/submissions/6c4bdaea-9005-4f39-9371-5d2ccaa0d354

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerImage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityPointCoverage
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationStalkDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehler_nativeNoPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehler_localClear
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_submodule_mem_of_forall_maximal_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityNormalChart_allMaximalPoints


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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (omega : KaehlerDifferential ℂ K) :
    omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ↔
      ∀ x : S, 0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x.val)
        (lpsOriginalNativeCovectorToLocal N hN x.val
          (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  constructor
  · intro h x
    exact lpsOriginalInfinityAffineKaehler_nativeNoPole N hpos hN x.val x.property omega h
  · intro h
    apply submodule_mem_of_forall_maximal_clear R (KaehlerDifferential ℂ K)
      (KaehlerDifferential.map ℂ ℂ R K).range omega
    intro M hM
    obtain ⟨x,hx⟩ := lpsOriginalInfinityNormalChart_allMaximalPoints N hpos hN M
    obtain ⟨s,hs,hsomega⟩ := lpsOriginalInfinityAffineKaehler_localClear N hpos hN
      x.val x.property omega (h x)
    exact ⟨s,by rwa [hx],hsomega⟩
end QEC.Coding.TannerLiftedProduct

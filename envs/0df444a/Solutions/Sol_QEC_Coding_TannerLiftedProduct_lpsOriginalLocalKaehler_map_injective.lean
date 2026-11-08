-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalLocalKaehler_map_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:30:11.293448+00:00
-- url     : https://prove2.me/submissions/5d06aed4-675a-4001-b983-658df0d616d8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicValuationDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicValuationRing_essFiniteType
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_LocalMeromorphicDifferential_localValuationKaehler_map_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary008
variable (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary016
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerInjectiveDictionary023
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (KaehlerDifferential.map ℂ ℂ V K) := by
  let : Algebra ℂ
      (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationRing K a) :=
    (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.complexConstantsToValuationRing K a).toAlgebra
  let : Algebra.EssFiniteType ℂ
      (QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationRing K a) := by
    change Algebra.EssFiniteType ℂ V
    exact lpsOriginalMeromorphicValuationRing_essFiniteType N hpos hN x
  exact QEC.Coding.AlgebraicGeometry.LocalMeromorphicDifferential.localValuationKaehler_map_injective K a
end QEC.Coding.TannerLiftedProduct

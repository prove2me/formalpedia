-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroAffineKaehler_kernel_clear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:34:09.477212+00:00
-- url     : https://prove2.me/submissions/e726d65f-9a3d-4180-ac7c-735f40d89cfb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalAffineKaehlerInjective
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_kaehler_field_map_zero_heightOne_clear
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLocalKaehler_map_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary016
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalAffineKaehlerInjectiveDictionary024
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X))
    (tau : KaehlerDifferential ℂ R) (hzero : KaehlerDifferential.map ℂ ℂ R K tau = 0) :
    ∃ s : R, s ∉ RingHom.ker (lpsOriginalZeroNormalChartEvaluation N hpos hN x hj) ∧
      s • tau = 0 := by
  exact kaehler_field_map_zero_heightOne_clear ℂ R K
    (lpsOriginalZeroHeightOneCentre N hpos hN x hj) V
    (lpsOriginalZeroHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
    (lpsOriginalLocalKaehler_map_injective N hpos hN x) tau hzero
end QEC.Coding.TannerLiftedProduct

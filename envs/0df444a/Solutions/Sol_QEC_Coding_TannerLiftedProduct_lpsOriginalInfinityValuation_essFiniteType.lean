-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityValuation_essFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:19:04.147289+00:00
-- url     : https://prove2.me/submissions/916b36b6-885d-429f-8012-cb36c53abd90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerFiniteness
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_finiteType
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_heightOne_valuation_essFiniteType


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary027
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalInfinityChart N hpos
local notation "S" => lpsOriginalInfinityRegularPoints N hpos hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary028
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary029
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary030
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary031
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary032
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary033
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary034
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary035
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary036
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary037
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary038
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary039
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary040
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary041
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary042
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary043
variable (x : LPSOriginalFilledCurve N)
local notation "V" => Valuation.valuationSubring
  (AddValuation.toValuation (lpsOriginalFieldLocalOrder N hN hpos x))
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary044
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary045
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary046
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary047
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary048
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary049
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary050
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalLocalKaehlerFinitenessDictionary051
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (hj : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)⁻¹) :
    Algebra.EssFiniteType ℂ V := by
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact heightOne_valuation_essFiniteType ℂ R K
    (lpsOriginalInfinityHeightOneCentre N hpos hN x hj) V
    (lpsOriginalInfinityHeightOneCentre_valuationRing N hpos hN x hj) (fun _ => rfl)
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalTwoAffineKaehlerRanges_iff_allNativeNoPole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:26:54.908339+00:00
-- url     : https://prove2.me/submissions/e6d00f76-5ef5-478a-9572-ee0e4f4750ba

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalZeroAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalInfinityAffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalTwoChartDifferentials
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFieldJ_inverse_cusp_order_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityAffineKaehlerRange_iff_nativeNoPole
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "R" => lpsOriginalComplexNormalZeroChart N hpos
local notation "Q" => MulAction.orbitRel.Quotient
  (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary013
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary016
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary017
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary018
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary019
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary020
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary021
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary022
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary023
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary024
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary025
attribute [local instance] QEC.Coding.TannerLiftedProduct.LPSOriginalTwoChartDifferentialsDictionary026
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (omega : KaehlerDifferential ℂ K) :
    (omega ∈ (KaehlerDifferential.map ℂ ℂ R K).range ∧
      omega ∈ (KaehlerDifferential.map ℂ ℂ I K).range) ↔
      ∀ x : LPSOriginalFilledCurve N,
        0 ≤ meromorphicOrderValuation (lpsOriginalLocalChartCenter N hN x)
          (lpsOriginalNativeCovectorToLocal N hN x
            (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN omega)) := by
  rw [lpsOriginalZeroAffineKaehlerRange_iff_interiorNativeNoPole N hpos hN,
    lpsOriginalInfinityAffineKaehlerRange_iff_nativeNoPole N hpos hN]
  constructor
  · rintro ⟨hz,hi⟩ (x | c)
    · exact hz x
    · exact hi ⟨Sum.inr c,lpsOriginalFieldJ_inverse_cusp_order_nonnegative N hpos hN c⟩
  · intro h
    exact ⟨fun x => h (Sum.inl x), fun x => h x.val⟩
end QEC.Coding.TannerLiftedProduct

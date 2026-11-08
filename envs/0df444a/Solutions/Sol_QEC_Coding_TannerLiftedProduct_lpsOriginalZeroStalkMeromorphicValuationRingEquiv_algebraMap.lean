-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroStalkMeromorphicValuationRingEquiv_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:46:01.160532+00:00
-- url     : https://prove2.me/submissions/d09bab54-5355-4f64-af74-d687aaaa198c

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationComplexPoints
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ValuationCentres
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationLocalRings
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_ValuationCentres_heightOneStalkValuationRingEquiv_algebraMap


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open QEC.Coding.AlgebraicGeometry.ValuationCentres
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_22
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_27
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_28
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_29
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_30
local notation "IC0" => lpsOriginalComplexNormalZeroChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_59
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_60
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_112
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_82cf6a41b6_113
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : LPSOriginalFilledCurve N)
    (h : 0 ≤ lpsOriginalFieldLocalOrder N hN hpos x (algebraMap P K Polynomial.X)) (a : IC0) :
    ((lpsOriginalZeroStalkMeromorphicValuationRingEquiv N hpos hN x h)
      (algebraMap IC0 ((_root_.AlgebraicGeometry.Spec.structureSheaf IC0).presheaf.stalk
        (⟨(lpsOriginalZeroHeightOneCentre N hpos hN x h).asIdeal,
          (lpsOriginalZeroHeightOneCentre N hpos hN x h).isPrime⟩ : PrimeSpectrum IC0)) a)).val = a.val := by
  change ((heightOneStalkValuationRingEquiv IC0 (lpsOriginalZeroHeightOneCentre N hpos hN x h))
    (algebraMap IC0 _ a)).val = a.val
  exact heightOneStalkValuationRingEquiv_algebraMap IC0 (lpsOriginalZeroHeightOneCentre N hpos hN x h) a
end QEC.Coding.TannerLiftedProduct

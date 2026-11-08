-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_functionTimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:30:17.599457+00:00
-- url     : https://prove2.me/submissions/27bb04d0-e35d-4479-b272-91e8cfbb9b85

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorLinearEquiv_class
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorRatioMap_functionTimes


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold ContDiff TensorProduct
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_28
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "M" => LPSOriginalMeromorphicGermRing UpperHalfPlane.upperHalfPlaneSet
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_35
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_36
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_37
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_70
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_f7e67548a0_74
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (f : K) (differentialForm : KaehlerDifferential ℂ K)
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (sectionForm : LPSOriginalFilledMeromorphicCovectorRepresentatives N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f)
    (hsection : lpsOriginalCompactMeromorphicCovectorClass N hN sectionForm =
      lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN (f • differentialForm) =
      lpsOriginalCompactMeromorphicCovectorClass N hN
        (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F sectionForm) := by
  apply (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).injective
  rw [lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio,
    map_smul,lpsOriginalCompactMeromorphicCovectorLinearEquiv_class,
    lpsOriginalCompactMeromorphicCovectorRatioMap_functionTimes,hF]
  have hs := congrArg (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN) hsection
  rw [lpsOriginalCompactMeromorphicCovectorLinearEquiv_class,
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio] at hs
  rw [hs]
  change lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
    (f * lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) = _
  exact map_mul _ _ _
end QEC.Coding.TannerLiftedProduct

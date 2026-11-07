-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:50:03.399894+00:00
-- url     : https://prove2.me/submissions/1b7c32f4-9bb8-4b4f-846b-5bd137ba568e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison

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
    (differentialForm : KaehlerDifferential ℂ K) :
    lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN
      (lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN differentialForm) =
        lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
          (lpsOriginalGenericKaehlerCoefficientEquiv N hpos differentialForm) := by
  exact (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).apply_symm_apply _
end QEC.Coding.TannerLiftedProduct

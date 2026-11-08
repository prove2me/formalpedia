-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv_j
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:57:03.64071+00:00
-- url     : https://prove2.me/submissions/da550285-732f-48cb-96ac-598d301f6218

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericToMeromorphicGerm_j


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
theorem _root_.solution :
    lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN
      (algebraMap P K Polynomial.X) =
        lpsOriginalCompactMeromorphicGermAlgHom N hN
          ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩ := by
  apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
  apply Subtype.ext
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
      (algebraMap P K Polynomial.X))).val =
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict
        ⟨lpsOriginalFilledJ N,lpsOriginalFilledChartMeromorphic_j N hN⟩)).val
  rw [lpsOriginalGeneratedCompactMeromorphic_restrict,
    lpsOriginalGenericToMeromorphicGerm_j,lpsOriginalCompactToRestrictedMeromorphic_apply]
  rfl
end QEC.Coding.TannerLiftedProduct

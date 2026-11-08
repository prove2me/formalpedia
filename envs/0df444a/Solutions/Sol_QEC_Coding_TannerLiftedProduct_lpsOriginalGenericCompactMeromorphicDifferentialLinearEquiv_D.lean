-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:59:50.532141+00:00
-- url     : https://prove2.me/submissions/84ee2493-3a41-4faa-998d-21529e96826a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorLinearEquiv_class
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGenericJDerivation_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJMeromorphicDerivative_ne_zero


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
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv N hpos hN
      (KaehlerDifferential.D ℂ K f) =
        lpsOriginalCompactMeromorphicCovectorClass N hN
          ⟨lpsOriginalFilledFunctionCovector N hN F.val,
            lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ := by
  apply (lpsOriginalCompactMeromorphicCovectorLinearEquiv N hN).injective
  rw [lpsOriginalGenericCompactMeromorphicDifferentialLinearEquiv_ratio,
    lpsOriginalCompactMeromorphicCovectorLinearEquiv_class]
  apply lpsOriginalCompactToRestrictedMeromorphic_injective N hN
  apply Subtype.ext
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN
      (lpsOriginalGenericKaehlerCoefficientEquiv N hpos (KaehlerDifferential.D ℂ K f)))).val = _
  rw [lpsOriginalGeneratedCompactMeromorphic_restrict]
  change lpsOriginalGenericToMeromorphicGerm N hpos
    (lpsOriginalGenericJDerivation N hpos f) = _
  have hrepr := congrArg (fun g : L => (lpsOriginalCompactToRestrictedMeromorphic N hN g).val) hF
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict F)).val =
      (lpsOriginalCompactToRestrictedMeromorphic N hN
        (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f)).val at hrepr
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply,
    lpsOriginalGeneratedCompactMeromorphic_restrict] at hrepr
  have hratio := lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict N hN F
  rw [hrepr,lpsOriginalGenericJDerivation_meromorphic] at hratio
  exact (mul_right_cancel₀ lpsOriginalJMeromorphicDerivative_ne_zero hratio).symm
end QEC.Coding.TannerLiftedProduct

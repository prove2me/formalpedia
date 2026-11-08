-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedRestriction_representative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:25:10.742258+00:00
-- url     : https://prove2.me/submissions/5eded2c9-7b37-4420-a1dc-dc372ab04437

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalMeromorphicOrder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFieldIntegral

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary001
local notation "K" => lpsOriginalGeneratedFunctionField N hpos
local notation "J" => FractionRing (Polynomial ℂ)
local notation "P" => Polynomial ℂ
local notation "E" => lpsOriginalFilledMeromorphicRestrictionSubfield N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary002
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalFieldIntegralDictionary003
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (f : K) (F : LPSOriginalFilledMeromorphicFunctionRing N hN)
    (hF : lpsOriginalCompactMeromorphicGermAlgHom N hN F =
      lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) :
    lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f =
      lpsOriginalFilledMeromorphicRestriction N hN F.val F.property := by
  have he : (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      (lpsOriginalGeneratedCompactMeromorphicEquiv N hpos hN f) =
      lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f := by
    change (lpsOriginalCompactRestrictedMeromorphicEquiv N hN)
      ((lpsOriginalCompactRestrictedMeromorphicEquiv N hN).symm
        (lpsOriginalGeneratedRestrictionPolynomialAlgEquiv N hpos hN f)) = _
    exact RingEquiv.apply_symm_apply _ _
  rw [←he]
  change lpsOriginalCompactToRestrictedMeromorphic N hN
    (lpsOriginalGeneratedCompactMeromorphicComplexAlgEquiv N hpos hN f) = _
  rw [←hF]
  exact lpsOriginalCompactToRestrictedMeromorphic_apply N hN F
end QEC.Coding.TannerLiftedProduct

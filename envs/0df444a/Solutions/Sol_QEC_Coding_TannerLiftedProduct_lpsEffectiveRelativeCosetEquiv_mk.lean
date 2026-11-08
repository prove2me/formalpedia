-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveRelativeCosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:26.259512+00:00
-- url     : https://prove2.me/submissions/519ea20c-104d-4263-a6da-e399f7954c48

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveRelativeCosets

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (H : Subgroup SL(2,ℤ))
    (hker : (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.ker ≤ H)
    (γ : CongruenceSubgroup.Gamma0 N) :
    lpsEffectiveRelativeCosetEquiv N H hker (QuotientGroup.mk γ) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict.subgroupMap
        (CongruenceSubgroup.Gamma0 N) γ) := rfl
end QEC.Coding.TannerLiftedProduct

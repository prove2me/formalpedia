-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveGamma0CosetEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:54:49.896209+00:00
-- url     : https://prove2.me/submissions/4d7c8c38-4ac5-46ea-a63d-b08f75ab8c2e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (h : SL(2,ℤ)) :
    lpsEffectiveGamma0CosetEquiv N (QuotientGroup.mk h) =
      QuotientGroup.mk ((MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict h) := rfl
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveSubgroup_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:26.495342+00:00
-- url     : https://prove2.me/submissions/cb06e872-3296-4ba9-b1bb-bb91689903de

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup SL(2,ℤ)) :
    (H.map (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict).map
      lpsEffectiveModularGroup.subtype=H.map (MulAction.toPermHom SL(2,ℤ) ℍ) := by
  let φ : SL(2,ℤ) →* lpsEffectiveModularGroup :=
    (MulAction.toPermHom SL(2,ℤ) ℍ).rangeRestrict
  change (H.map φ).map lpsEffectiveModularGroup.subtype=_
  rw [Subgroup.map_map]
  rfl
end QEC.Coding.TannerLiftedProduct

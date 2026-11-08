-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_of_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:07:06.646854+00:00
-- url     : https://prove2.me/submissions/27a0d3a9-94dd-4543-9375-3f857de75473

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (H : Subgroup lpsEffectiveModularGroup)
    {s : Set ℍ} (hs : IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume) :
    IsFundamentalDomain H s volume := by
  let e := H.equivMapOfInjective lpsEffectiveModularGroup.subtype
    lpsEffectiveModularGroup.subtype_injective
  refine hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id volume) e.symm.bijective ?_
  intro g τ
  have he := congrArg (fun π : H.map lpsEffectiveModularGroup.subtype => (π:Equiv.Perm ℍ) τ)
    (e.apply_symm_apply g)
  exact he
end QEC.Coding.TannerLiftedProduct

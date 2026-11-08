-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsEffectiveFundamental_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:05.926286+00:00
-- url     : https://prove2.me/submissions/4761f25b-ffe3-4ebf-a6d4-3a69fee2ee5d

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
    {s : Set ℍ} (hs : IsFundamentalDomain H s volume) :
    IsFundamentalDomain (H.map lpsEffectiveModularGroup.subtype) s volume :=
  hs.preimage_of_equiv (Measure.QuasiMeasurePreserving.id volume)
    (H.equivMapOfInjective lpsEffectiveModularGroup.subtype
      lpsEffectiveModularGroup.subtype_injective).bijective (fun _ _ => rfl)
end QEC.Coding.TannerLiftedProduct

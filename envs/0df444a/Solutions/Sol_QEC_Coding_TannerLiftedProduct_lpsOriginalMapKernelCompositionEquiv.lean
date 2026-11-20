-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalMapKernelCompositionEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:58:49.337677+00:00
-- url     : https://prove2.me/submissions/073a7aa0-8e37-406e-84c8-94b3d80e6087

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFrobeniusDescent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (e : R ≃+* A) (f : A →+* B) :
    (RingHom.ker (f.comp e.toRingHom)).map e = RingHom.ker f := by
  have h : RingHom.ker (f.comp e.toRingHom) = (RingHom.ker f).comap e := by
    ext x
    rfl
  rw [h]
  exact (RingHom.ker f).map_comap_eq_self_of_equiv e
end QEC.Coding.TannerLiftedProduct

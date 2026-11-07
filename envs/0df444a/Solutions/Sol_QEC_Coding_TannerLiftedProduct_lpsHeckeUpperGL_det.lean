-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:10.955624+00:00
-- url     : https://prove2.me/submissions/103e58fe-ce16-46c5-9cb3-699299cc5fcc

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckeUpperGL_coe

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i).det.val=(p:R) := by
  change ((lpsHeckeUpperGL R p i : Matrix (Fin 2) (Fin 2) R).det)=_
  rw [lpsHeckeUpperGL_coe,Int.coe_castRingHom,←Int.cast_det,lpsHeckeUpperMatrix_det]
  simp
end QEC.Coding.TannerLiftedProduct

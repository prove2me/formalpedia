-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeUpperGL_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:45:07.831269+00:00
-- url     : https://prove2.me/submissions/10920bd8-3e76-4664-b9ad-ab89782fc11c

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i : Option (Fin p)) :
    (lpsHeckeUpperGL R p i : Matrix (Fin 2) (Fin 2) R)=
      (lpsHeckeUpperMatrix p i).map (Int.castRingHom R) := rfl
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsHeckeRightFactorGL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:41:35.755395+00:00
-- url     : https://prove2.me/submissions/2d553dbc-6d32-4c13-952e-92ac860722c1

import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.ModularForms.NormTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeRepresentatives

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (R : Type*) [Field R] [CharZero R]
    (p : ℕ) [Fact p.Prime] (i j : Option (Fin p)) (γ δ : SL(2,ℤ))
    (h : lpsHeckeUpperMatrix p i*(γ:Matrix (Fin 2) (Fin 2) ℤ)=
      (δ:Matrix (Fin 2) (Fin 2) ℤ)*lpsHeckeUpperMatrix p j) :
    lpsHeckeUpperGL R p i*Matrix.SpecialLinearGroup.mapGL R γ=
      Matrix.SpecialLinearGroup.mapGL R δ*lpsHeckeUpperGL R p j := by
  apply Units.ext
  change (lpsHeckeUpperMatrix p i).map (Int.castRingHom R)*
      (γ:Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R)=
    (δ:Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom R)*
      (lpsHeckeUpperMatrix p j).map (Int.castRingHom R)
  simpa only [Matrix.map_mul] using congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (Int.castRingHom R)) h
end QEC.Coding.TannerLiftedProduct

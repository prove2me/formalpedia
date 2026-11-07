-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionInversion_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:27:39.540917+00:00
-- url     : https://prove2.me/submissions/2804271f-5ca6-4e1f-8f3c-8087bdb914b3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Involutive lpsOriginalJFractionInversion := by
  have h : lpsOriginalJFractionInversion.comp lpsOriginalJFractionInversion=
      RingHom.id (FractionRing (Polynomial ℚ)) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℚ)
    have hp : (lpsOriginalJFractionInversion.comp
        lpsOriginalJFractionInversion).comp
        (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))=
        algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) := by
      apply Polynomial.ringHom_ext
      · intro q
        change lpsOriginalJFractionInversion
            (lpsOriginalJFractionInversion
              (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) (Polynomial.C q)))=_
        rw [Polynomial.C_eq_algebraMap,
          ←IsScalarTower.algebraMap_apply ℚ (Polynomial ℚ) (FractionRing (Polynomial ℚ))]
        change lpsOriginalJFractionInversion
            (lpsOriginalJFractionInversion
              (algebraMap ℚ (FractionRing (Polynomial ℚ)) q))=
          algebraMap ℚ (FractionRing (Polynomial ℚ)) q
        rw [RingHom.map_rat_algebraMap,RingHom.map_rat_algebraMap]
      · change lpsOriginalJFractionInversion
          (lpsOriginalJFractionInversion
            (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) Polynomial.X))=_
        rw [lpsOriginalJFractionInversion_X,map_inv₀,
          lpsOriginalJFractionInversion_X,inv_inv]
    intro P
    exact RingHom.congr_fun hp P
  intro x
  exact RingHom.congr_fun h x
end QEC.Coding.TannerLiftedProduct

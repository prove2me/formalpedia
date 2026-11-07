-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJLineToSpecZ_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:03:38.136716+00:00
-- url     : https://prove2.me/submissions/09833548-1721-4767-9293-ca76679779dc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ


set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Surjective lpsOriginalIntegerProjectiveJLineToSpecZ := by
  constructor
  intro y
  refine ⟨lpsOriginalIntegerProjectiveJAffinePoint ℤ false 0 y, ?_⟩
  have h := lpsOriginalIntegerProjectiveJAffinePoint_toSpecZ ℤ false 0
  have hi : Spec.map (CommRingCat.ofHom (Int.castRingHom ℤ)) = 𝟙 (Spec (.of ℤ)) := by
    have hr : Int.castRingHom ℤ = RingHom.id ℤ := Subsingleton.elim _ _
    rw [hr]
    exact Spec.map_id _
  exact congrArg (fun f : Spec (.of ℤ) ⟶ Spec (.of ℤ) => f y) (h.trans hi)
end QEC.Coding.TannerLiftedProduct

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_constantRingHomProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:55.828144+00:00
-- url     : https://prove2.me/submissions/9f535f09-7ee0-4295-a3f5-094e805a09b8

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
theorem _root_.solution (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (normalizationConstantRingHom e.toRingHom)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  rfl
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

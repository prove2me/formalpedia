-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_scalarProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:49.839204+00:00
-- url     : https://prove2.me/submissions/c84244cd-6b4d-46ea-bfb6-e51aa5d3dd6b

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
variable {R S A B : Type} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra S B]
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
theorem _root_.solution (e : S ⊗[R] A ≃ₐ[S] B) :
    (normalizationTensorSpecIso e).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S B)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.fst _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact e.commutes c
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

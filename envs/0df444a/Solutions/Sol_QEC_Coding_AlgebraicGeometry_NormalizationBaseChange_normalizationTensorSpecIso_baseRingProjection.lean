-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:12:40.223986+00:00
-- url     : https://prove2.me/submissions/29f4dd10-88db-483b-bb41-a60568e65399

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
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom)) := by
  change (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    (pullbackSpecIso R S A).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

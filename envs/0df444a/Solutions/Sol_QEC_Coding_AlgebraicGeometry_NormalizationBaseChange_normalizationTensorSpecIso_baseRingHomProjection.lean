-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationTensorSpecIso_baseRingHomProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:50.807206+00:00
-- url     : https://prove2.me/submissions/bc1f2914-dc68-434f-a706-21d2f7df6c1f

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_baseRingProjection

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
    (normalizationTensorSpecIso e).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (normalizationBaseRingHom e.toRingHom)) := by
  rw [normalizationTensorSpecIso_baseRingProjection]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.normalizationConstantRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:48.866343+00:00
-- url     : https://prove2.me/submissions/51941043-157f-426b-be15-f60727013b5b

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
open scoped TensorProduct
variable {R₀ S₀ A₀ D₀ : Type} [CommRing R₀] [CommRing S₀] [CommRing A₀] [CommRing D₀]
  [Algebra R₀ S₀] [Algebra R₀ A₀]
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
theorem _root_.solution (e : S₀ ⊗[R₀] A₀ →+* D₀) (c : S₀) :
    normalizationConstantRingHom e c = e (c ⊗ₜ[R₀] (1 : A₀)) := rfl
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

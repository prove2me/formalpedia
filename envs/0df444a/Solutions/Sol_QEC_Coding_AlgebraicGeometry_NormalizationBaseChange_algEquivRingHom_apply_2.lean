-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.NormalizationBaseChange.algEquivRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:26:47.090062+00:00
-- url     : https://prove2.me/submissions/fedb25ca-de94-4807-b537-c519d44b7f08

import Mathlib.AlgebraicGeometry.Pullbacks
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
namespace QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
theorem _root_.solution (e : A ≃ₐ[R] B) (x : A) : e.toRingHom x = e x := rfl
end QEC.Coding.AlgebraicGeometry.NormalizationBaseChange

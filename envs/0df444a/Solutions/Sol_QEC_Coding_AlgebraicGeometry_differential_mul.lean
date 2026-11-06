-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differential_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:15:00.065916+00:00
-- url     : https://prove2.me/submissions/aae862e3-d940-47b7-b624-6e8379657395

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution (f g : F) :
    differential k F (f * g) = f • differential k F g + g • differential k F f := by
  exact (KaehlerDifferential.D k F).leibniz f g
end QEC.Coding.AlgebraicGeometry

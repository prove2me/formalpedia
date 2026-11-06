-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.differential_span_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:27:54.238753+00:00
-- url     : https://prove2.me/submissions/97222c15-a9b7-44e8-bc75-3a9ce4e18553

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution :
    Submodule.span F (Set.range (differential k F)) = ⊤ := by
  change Submodule.span F (Set.range (KaehlerDifferential.D k F)) = ⊤
  exact KaehlerDifferential.span_range_derivation k F
end QEC.Coding.AlgebraicGeometry

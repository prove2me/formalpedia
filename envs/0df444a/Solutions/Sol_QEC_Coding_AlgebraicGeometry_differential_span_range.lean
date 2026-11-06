-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differential_span_range
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:57:38.598512+00:00
-- url     : https://prove2.me/submissions/b523b3f4-6ad5-4eaf-9773-2326f48b3a6f

import Mathlib.RingTheory.Kaehler.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_SeparableDerivationExtension
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_Differential
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable (k F : Type*) [Field k] [Field F] [Algebra k F]

theorem solution :
    Submodule.span F (Set.range (differential k F)) = ⊤ := by
  exact KaehlerDifferential.span_range_derivation k F

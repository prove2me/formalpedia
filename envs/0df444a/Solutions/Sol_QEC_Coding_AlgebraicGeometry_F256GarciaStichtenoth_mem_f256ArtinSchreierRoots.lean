-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.mem_f256ArtinSchreierRoots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:48:40.540423+00:00
-- url     : https://prove2.me/submissions/e4c75813-56b2-4f8d-abee-bc148793b85a

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Field
import Mathlib.FieldTheory.Finite.Trace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (x y : F256) :
    y ∈ f256ArtinSchreierRoots x ↔ y ^ 16 + y = x ^ 17 := by
  simp [f256ArtinSchreierRoots, f256ArtinSchreier_apply]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

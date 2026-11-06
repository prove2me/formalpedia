-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseField_seed_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:23:36.432086+00:00
-- url     : https://prove2.me/submissions/0a288d46-f1fc-4eca-9251-c7c59c24233f

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_galoisBaseField_ratFunc_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceField_finrank


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    Module.finrank GaloisBaseField (SourceField m) = 240 * 16 ^ m := by
  calc
    Module.finrank GaloisBaseField (SourceField m) =
        Module.finrank GaloisBaseField (RatFunc F256) *
          Module.finrank (RatFunc F256) (SourceField m) :=
      (Module.finrank_mul_finrank GaloisBaseField (RatFunc F256)
        (SourceField m)).symm
    _ = 240 * 16 ^ m := by
      rw [galoisBaseField_ratFunc_finrank, sourceField_finrank]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

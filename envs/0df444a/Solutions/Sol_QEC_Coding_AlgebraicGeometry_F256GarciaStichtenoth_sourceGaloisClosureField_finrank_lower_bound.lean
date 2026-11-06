-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_finrank_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:27:13.763808+00:00
-- url     : https://prove2.me/submissions/d31a1ef0-d3dc-45dc-bfcb-46f9496ac019

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRecursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisSeedSeparable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.SeparableClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisBaseField_seed_finrank

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank GaloisBaseField (SourceGaloisClosureField m) := by
  rw [← sourceGaloisBaseField_seed_finrank m]
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (sourceGaloisSeedToClosure m).toLinearMap)
    (sourceGaloisSeedToClosure m).injective
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

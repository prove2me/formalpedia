-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisClosureField_ratFunc_finrank_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:17.842371+00:00
-- url     : https://prove2.me/submissions/220d33a7-2e40-4d00-82ef-503da0be7e28

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceNormalClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceGaloisFunctionField
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_ratFunc_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceGaloisClosureField_finrank_lower_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    240 * 16 ^ m ≤
      Module.finrank (RatFunc F256) (SourceGaloisClosureField m) := by
  rw [sourceGaloisClosureField_ratFunc_finrank]
  exact sourceGaloisClosureField_finrank_lower_bound m
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

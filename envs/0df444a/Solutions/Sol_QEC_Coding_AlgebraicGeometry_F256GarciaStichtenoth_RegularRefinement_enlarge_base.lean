-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.enlarge_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:22:51.520749+00:00
-- url     : https://prove2.me/submissions/0a907525-c46a-44d2-9125-bdb615678cb4

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_enlarge_base
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularRefinement_le

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularRefinement
theorem _root_.solution {K L M : IntermediateField F E}
    (h : RegularRefinement Q K L) (hKM : K ≤ M) :
    RegularRefinement Q M (M ⊔ L) := by
  induction h with
  | refl => rw [sup_eq_left.mpr hKM]
  | @tail L N hchain hstep ih =>
      have hs := hstep.enlarge_base Q (show L ≤ M ⊔ L from le_sup_right)
      rw [sup_assoc, sup_eq_right.mpr (hstep.le Q)] at hs
      exact ih.tail hs
end RegularRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

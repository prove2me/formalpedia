-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularRefinement.le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:16:19.841499+00:00
-- url     : https://prove2.me/submissions/3c09631e-c3c9-4b79-bc87-378e816a5967

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_RegularQuadraticEdge_le

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularRefinement
theorem _root_.solution {K L : IntermediateField F E}
    (h : RegularRefinement Q K L) : K ≤ L := by
  induction h with
  | refl => exact le_rfl
  | tail h hstep ih => exact ih.trans (hstep.le Q)
end RegularRefinement
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

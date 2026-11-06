-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:12:40.329503+00:00
-- url     : https://prove2.me/submissions/1f6c56fe-f9cb-4cc7-ba0e-66221f1a7303

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_TraceRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_RegularRefinement

set_option autoImplicit false
open IntermediateField
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {F E : Type*} [_root_.Field F] [_root_.Field E] [Algebra F E]
  [Algebra F256 E] (Q : GlobalPlace F256 E)
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
namespace RegularQuadraticEdge
theorem _root_.solution {K L : IntermediateField F E}
    (h : RegularQuadraticEdge Q K L) : K ≤ L := by
  obtain ⟨y, _, _, rfl⟩ := h
  exact le_sup_left
end RegularQuadraticEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth

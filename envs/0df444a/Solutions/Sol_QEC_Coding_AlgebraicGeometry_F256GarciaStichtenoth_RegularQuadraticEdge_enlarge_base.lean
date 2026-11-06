-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.RegularQuadraticEdge.enlarge_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:17:08.247204+00:00
-- url     : https://prove2.me/submissions/cfc2d846-01bd-400b-984e-53af9468fa19

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
theorem _root_.solution {K L M : IntermediateField F E}
    (h : RegularQuadraticEdge Q K L) (hKM : K ≤ M) :
    RegularQuadraticEdge Q M (M ⊔ L) := by
  obtain ⟨y, hy, ha, rfl⟩ := h
  refine ⟨y, hy, hKM ha, ?_⟩
  rw [← sup_assoc, sup_eq_left.mpr hKM]
end RegularQuadraticEdge
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
